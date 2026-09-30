# Frobenius elements, Chebotarev density, and finite-image Galois representations

**Status.** Mathematical exposition, pinned to the FLT pin `aa2d8b3`. This note is
about the mathematics of one subject of the weight-one cone: the vocabulary of
Frobenius elements at a place, the qualitative density theorem that governs them,
and the two representation-theoretic consequences the Deligne–Serre argument
needs. Line numbers refer to `anthropics/fermats-last-theorem@aa2d8b3`; Mathlib
names refer to the pin's `v4.33.0`.

Companions: [019-deligne-serre-weight-one.md](019-deligne-serre-weight-one.md)
(the weight-one correspondence and the assembly this subject serves),
[003-galois-rep-irreducible-in-english.md](003-galois-rep-irreducible-in-english.md)
and [004-irreducible-and-cofixed-line.md](004-irreducible-and-cofixed-line.md)
(the irreducibility vocabulary), [006-fixed-or-cofixed-and-inertia.md](006-fixed-or-cofixed-and-inertia.md)
(decomposition and inertia), [011-tate-module.md](011-tate-module.md) (the
$`\ell`$-adic representations this subject compares with).

## 1. The problem this subject solves

The weight-one theorem attaches to a normalized cuspidal newform $`f`$ of level
$`N`$ a Galois representation

$$\\rho_f : G_{\\mathbb{Q}} = \\mathrm{Gal}(\\overline{\\mathbb{Q}}/\\mathbb{Q})
\\longrightarrow \\mathrm{GL}_2(\\mathbb{C})$$

of **finite image**, characterized by

$$\\mathrm{charpoly}\\bigl(\\rho_f(\\mathrm{Frob}_p)\\bigr) = X^2 - a_p X + \\varepsilon(p)
\\qquad (p \\nmid N),$$

where $`a_p`$ are the Hecke eigenvalues and $`\varepsilon`$ the nebentypus. Three
facts have to be established before such a sentence even names a well-defined
object.

1. **What is $`\mathrm{Frob}_p`$?** At each rational prime $`p`$ one must choose a
   place of $`\overline{\mathbb{Q}}`$ above $`p`$; the resulting Frobenius element
   is canonical only up to conjugation and up to the inertia subgroup. One needs a
   vocabulary in which "the Frobenius at $`p`$" is a well-defined conjugacy class,
   and one needs to know when its action on a finite residue field has residue
   degree one.
2. **How do "almost all primes" become "the whole group"?** The data
   $`\{\mathrm{charpoly}(\rho(\mathrm{Frob}_p))\}_p`$ is given on a density-one
   set of group elements. To conclude that $`\rho`$ is, say, irreducible or
   conjugate to another representation, one must know that the Frobenius elements
   see all of the finite Galois group — this is the **density theorem**
   (Chebotarev, in Frobenius' qualitative form).
3. **How does a character know a representation?** For a finite group and a field
   of characteristic zero, equal characteristic polynomials at every element force
   conjugacy (Brauer–Nesbitt); for a residual representation over a finite field
   the analogous statement has to be run in reverse to *descend* a representation
   defined over a large field to a smaller one.

The subject of this note is the part of the weight-one cone that supplies exactly
these three things. Its statements are gathered in §8; §§2–7 are the mathematics.

Two structural remarks frame everything below.

* **Frobenius is not canonical, only its conjugacy class is.** For a fixed prime
   $`p`$, changing the chosen place conjugates $`\mathrm{Frob}_p`$, and only the
   coset modulo inertia is determined. Every classical statement is therefore
   either conjugation-invariant or explicitly existential over places.
* **The density theorem is an *analytic* theorem.** The qualitative form is
   deduced from the pole of the Dedekind zeta function at $`s = 1`$ (equivalently,
   from the prime ideal theorem for degree-one primes); the group theory
   contributes only a Möbius-inversion identity. This split — analysis in §5,
   combinatorics in §4 — is the shape of the proof, and it is where the formal
   weight of the subject sits.

## 2. Frobenius at a place

### 2.1 Places as valuation subrings

Work inside a fixed algebraic closure $`\overline{\mathbb{Q}}`$ and let
$`\Gamma_{\mathbb{Q}} = \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})`$. A
**place** above a rational prime $`p`$ is a valuation subring
$`A \subseteq \overline{\mathbb{Q}}`$ whose maximal ideal contains $`p`$; this
is the predicate `LiesOverPrime A p`, i.e. $`(p : \overline{\mathbb{Q}}) \in A^{\times}`$-complement
(`A.nonunits`). Equivalently $`A`$ is the localization
$`\mathcal{O}_{\overline{\mathbb{Q}},P}`$ at a prime $`P`$ of the integral
closure of $`\mathbb{Z}`$ in $`\overline{\mathbb{Q}}`$ lying over $`p`$ (this
identification is itself one of the statements below: every such place *is* a
localization).

For a place $`A`$ one has the **decomposition subgroup**
$`D_A = \mathrm{Stab}_{\Gamma_{\mathbb{Q}}}(A)`$ and the **inertia subgroup**
$`I_A \trianglelefteq D_A`$, which acts trivially on the residue field
$`\kappa(A) = A/\mathfrak{m}_A`$. For a number field $`L`$ there is the analogue
$`D_Q = \mathrm{Stab}_{\mathrm{Gal}(L/\mathbb{Q})}(Q)`$ and the inertia subgroup
$`I_Q`$ of a prime $`Q`$ of $`\mathcal{O}_L`$; the pin writes the image of the
inertia in the decomposition group of an ambient field as
`inertiaSubgroupIn`.

### 2.2 The Frobenius predicate

The residue field of a place above $`p`$ is an algebraic closure of $`\mathbb{F}_p`$,
so it carries the Frobenius automorphism $`x \mapsto x^p`$. The pin's definition is

> $`A.\mathrm{IsFrobeniusAt}\ \sigma\ p`$ holds when
> $`\sigma \in D_A`$ and the class of $`\sigma`$ in
> $`D_A/I_A \hookrightarrow \mathrm{Gal}(\kappa(A)/\mathbb{F}_p)`$ acts as
> $`x \mapsto x^p`$.

Two elementary facts make this the right definition.

* **Existence.** Every place above $`p`$ has a Frobenius: the decomposition group
  surjects onto the cyclic group $`\mathrm{Gal}(\kappa(A)/\mathbb{F}_p)`$
  generated by $`x \mapsto x^p`$. For $`\overline{\mathbb{Q}}`$ this is stated as
  the existence, for every prime $`p`$ and every place `A` over it, of a
  $`\sigma`$ with `A.IsFrobeniusAt σ p`; and there always *exists* a place over
  $`p`$.
* **Uniqueness up to inertia.** Two Frobenius elements at the same place differ by
  an element of $`I_A`$. At an unramified prime $`I_A = 1`$, and the Frobenius is a
  single well-defined element of $`D_A`$; at a place of residue degree one it
  generates $`D_A`$ (§3.1).

### 2.3 Lifting Frobenius from a number field

The density theorem is proved for a finite Galois number field $`E/\mathbb{Q}`$,
because that is where the analytic count of primes lives. But the representation
is a representation of the full group $`\Gamma_{\mathbb{Q}}`$. The bridge is the
following lifting statement.

> Let $`E \subseteq \overline{\mathbb{Q}}`$ be a finite Galois number field, let
> $`Q`$ be a prime of $`\mathcal{O}_E`$ over $`p`$ with finite residue field. Then
> there is a place $`A`$ of $`\overline{\mathbb{Q}}`$ over $`Q`$ and
> $`\tau \in D_A`$ with `A.IsFrobeniusAt τ p` whose restriction to $`E`$ is the
> arithmetic Frobenius `arithFrobAt` at $`Q`$.

This is `NumberField.exists_isFrobenius_lift_arithFrobAt`; the two conjuncts
$`\tau \cdot x \in A \Leftrightarrow x \in A`$ and
$`\tau \cdot x - x^p \in \mathfrak{m}_A`$ in its conclusion are the two halves
of "integral element whose class is Frobenius". Its role: a Frobenius class in a
finite quotient of $`\Gamma_{\mathbb{Q}}`$ can always be *realized* by an honest
Frobenius in $`\Gamma_{\mathbb{Q}}`$, so density statements about
$`\Gamma_{\mathbb{Q}}`$ can be tested on finite levels and vice versa. It is used
with the identification of a place with a localization
(`NumberField.exists_valuationSubring_eq_localization`) and with the criterion
`ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem` that recognizes a
proposed valuation subring as a place with a given Frobenius.

## 3. Frobenius on ideals: the counting identities

### 3.1 The decomposition group is generated by Frobenius

Let $`L/\mathbb{Q}`$ be finite Galois, $`p`$ a prime, and $`Q`$ a prime of
$`\mathcal{O}_L`$ over $`p`$ at which $`p`$ is unramified (trivial inertia). Then

$$\\mathrm{Stab}_{\\mathrm{Gal}(L/\\mathbb{Q})}(Q)
= \\langle \\mathrm{Frob}_Q \\rangle,$$

the cyclic subgroup generated by the arithmetic Frobenius
(`FrobeniusDensity.stabilizer_eq_zpowers_arithFrobAt`). This is the group-theoretic
form of the fundamental exact sequence of local Galois theory: on the residue
field the decomposition group acts through $`\mathrm{Gal}(\kappa(Q)/\mathbb{F}_p)`$,
which is cyclic of order equal to the residue degree $`f`$, generated by
$`x \mapsto x^p`$; unramifiedness makes the map injective on $`D_Q`$, and the
Frobenius has order exactly $`f`$.

The proof's one non-formal input is the standard order bound for finite fields:
if $`K`$ is a finite field and every $`x \in K`$ satisfies $`x^n = x`$ for some
$`n \gt 1`$, then $`|K| \le n`$, because $`K`$ consists of roots of
$`X^n - X`$. Applied to the residue extension this gives
$`f = |\kappa(Q)| \le \mathrm{order}(\mathrm{Frob}_Q)`$, and since the other
inequality is immediate, the subgroup generated by Frobenius has the cardinality
of $`D_Q`$. The same finite-field bound reappears in the residual representation
theory: it is the elementary reason a bounded-order Frobenius image can only be so
large.

### 3.2 Degree-one primes are fixed points

Now let $`E = L^H`$ be the fixed field of a subgroup $`H \le \mathrm{Gal}(L/\mathbb{Q})`$
(the pin's `IsGaloisGroup H E L`). Primes $`\mathfrak{q}`$ of $`\mathcal{O}_E`$
over $`p`$ correspond to $`D`$-orbits on the primes of $`\mathcal{O}_L`$ over
$`p`$, where $`D = \mathrm{Stab}(Q_0)`$ is the stabilizer of a chosen prime
$`Q_0`$. The condition that $`\mathfrak{q}`$ have **residue degree one**,
$`|\mathcal{O}_E/\mathfrak{q}| = p`$, is exactly the condition that the
corresponding orbit is fixed pointwise by $`D`$. The counting statement is

$$\\#\\{\\mathfrak{q} \\text{ over } p \\text{ in } E : |\\mathcal{O}_E/\\mathfrak{q}| = p\\}
= \\#\\{x \\in \\mathrm{Gal}(L/\\mathbb{Q})/H : \\forall d \\in D,\\ d \\cdot x = x\\},$$

(`FrobeniusDensity.ncard_degreeOne_primesOver_under`), and, using §3.1 to replace
$`D`$ by $`\langle \mathrm{Frob}_{Q_0}\rangle`$, the equivalent form

$$\\#\\{\\mathfrak{q} : |\\mathcal{O}_E/\\mathfrak{q}| = p\\}
= \\#\\{x \\in \\mathrm{Gal}(L/\\mathbb{Q})/H : \\mathrm{Frob}_{Q_0} \\cdot x = x\\}$$

(`FrobeniusDensity.ncard_degreeOne_primesOver_eq_ncard_frobFixed`). This is the
exact translation that lets an *analytic* count of primes (left-hand side, §5) be
compared with a *purely group-theoretic* fixed-point count (right-hand side, §4).
Note that only degree-one primes appear: the residue degree of $`\mathfrak{q}`$ is
read off from the action of the decomposition group, and "degree one" is the case
where that action is trivial.

## 4. The Möbius inversion identity

The group theory that converts fixed-point counts into conjugacy-class counts is a
single Möbius identity. Let $`G`$ be a finite group, $`\sigma \in G`$ of order
$`n`$, and write $`\mu`$ for the arithmetic Möbius function.

Its first form counts the generators of the cyclic subgroup:

$$\\sum_{f \\mid n} \\mu\\!\\left(\\frac{n}{f}\\right) f = \\varphi(n) \gt 0$$

(`FrobeniusDensity.sum_moebius_mul_pos`): the divisor sum is the Euler phi
function, and it is the Möbius inversion of $`n = \sum_{f \mid n} \varphi(f)`$.

The second form is the one actually consumed,
`FrobeniusDensity.weight_eq`. With `f` running over the divisors of $`n`$ and
$`\tau \in G`$,

$$\\sum_{f \\mid n} \\mu\\!\\left(\\frac{n}{f}\\right)
  f\\;\\#\\{x \\in G/\\langle \\sigma^{n/f}\\rangle : \\tau \\cdot x = x\\}
= \\#\\{g \\in G : \\exists k,\\ (k, n) = 1,\\ g\\,\\sigma^k\\,g^{-1} = \\tau\\}.$$

The proof is an inclusion–exclusion over the subgroups
$`\langle \sigma^{n/f} \rangle`$ of $`\langle \sigma \rangle`$:

* a coset-count first rewrites $`f \cdot \#\{x : \tau x = x\}`$ as the number of
  $`g`$ with $`g^{-1} \tau g \in \langle \sigma^{n/f} \rangle`$;
* summing with Möbius weights, the indicator
  $`\sum_f \mu(n/f)\,\mathbf{1}[g^{-1}\tau g \in \langle \sigma^{n/f}\rangle]`$
  is $`1`$ exactly when $`g^{-1}\tau g`$ lies in $`\langle \sigma \rangle`$ and
  has order $`n`$ — i.e. is a *generator* $`\sigma^k`$ with $`(k, n) = 1`$;
* reindexing $`g^{-1}\tau g`$ as $`g \sigma^k g^{-1}`$ gives the right-hand side.

The companion `FrobeniusDensity.ncard_conj_gen_ne_zero_iff` records the immediate
corollary used downstream: the conjugacy orbit counted above is nonempty if and
only if $`\tau`$ is conjugate to some $`\sigma^k`$ with $`(k, n) = 1`$. So the
Möbius weight is a *detector of conjugacy to a generator power*; this is precisely
what the Frobenius statement asserts of a prime, and the reason it is stated with
the $`k`$ coprime to the order rather than with $`\sigma`$ itself.

## 5. The analytic input: Dedekind zeta and the degree-one asymptotic

### 5.1 The Dirichlet series

For a number field $`L`$ the pin fixes the following objects.

* $`\mathrm{idealSum}(s) = \sum_{I \ne 0} N(I)^{-s}`$ over nonzero ideals — the
  Dedekind zeta series.
* $`\mathrm{primeSum}(s) = \sum_{\mathfrak{p}} N(\mathfrak{p})^{-s}`$ over
  height-one primes (the "Euler factor" sum).
* $`\mathrm{degOneCount}(\ell) = \#\{\mathfrak{q} \text{ over } \ell :
  |\mathcal{O}_L/\mathfrak{q}| = \ell\}`$ — the number of degree-one primes over
  $`\ell`$.
* $`\mathrm{degOneSum}(S_0, s) = \sum_{\ell \notin S_0}
  \mathrm{degOneCount}(\ell)\,\ell^{-s}`$, and $`\mathrm{cutSum}`$ the same sum
  restricted to a finite exceptional set $`S_0`$.
* $`\mathrm{tailSum}(s) = \sum_{N(\mathfrak{p}) \text{ not prime}}
  N(\mathfrak{p})^{-s}`$ — the primes of residue degree $`\ge 2`$.
* $`\mathrm{tailConst} = \sum_{\ell} \ell^{-2}`$ and the pointwise bound
  $`\mathrm{tailSum}(s) \le [L : \mathbb{Q}]\cdot\mathrm{tailConst}`$ for
  $`s \ge 1`$.

The decomposition

$$\\mathrm{primeSum}(s) = \\mathrm{degOneSum}(S_0, s) + \\mathrm{cutSum}(S_0, s)
+ \\mathrm{tailSum}(s)$$

(`FrobeniusDensity.primeSum_eq_degOneSum_add`) is the division of the prime sum
into the part whose behaviour is *governed by Frobenius* (degree one) and the part
that is bounded (the cut and the higher-degree tail). It is the reason
Chebotarev-type statements are statements about degree-one primes.

### 5.2 The pole at $`s = 1`$

The Dedekind zeta function has a simple pole at $`s = 1`$ with residue

$$\\rho_L = \\mathrm{res}_{s=1}\\,\\zeta_L(s)
= \\frac{2^{r_1}(2\\pi)^{r_2} h_L R_L}{w_L\\sqrt{|d_L|}},$$

the class number formula (the pin uses Mathlib's `dedekindZeta_residue`). Two
statements record this analytically.

* **Convergence.** $`\mathrm{idealSum}(s) \ne \top`$ for real $`s \gt 1`$
  (`FrobeniusDensity.idealSum_ne_top`). The proof identifies $`\mathrm{idealSum}`$
  with $`\sum_n \#\{I : N(I) = n\}\,n^{-s}`$ and uses
  $`\sum_{N(I) \le x} 1 = O(x)`$ — i.e. the residue — plus summability of the
  Dirichlet series of $`\zeta_L`$.
* **Residue.** $`(s - 1)\,\mathrm{idealSum}(s) \to \rho_L`$ as $`s \downarrow 1`$
  (`FrobeniusDensity.tendsto_sub_one_mul_idealSum_test`); this is the
  coefficientwise comparison with Mathlib's
  `tendsto_sub_one_mul_dedekindZeta_nhdsGT`.

From the Euler product one gets the prime sum: for $`s \gt 1`$,

$$\\log \\zeta_L(s) = -\\sum_{\\mathfrak{p}} \\log\\!\\left(1 - N(\\mathfrak{p})^{-s}\\right)
= \\mathrm{primeSum}(s) + O(1),$$

because the terms with $`N(\mathfrak{p})^{-ms}`$, $`m \ge 2`$, are dominated by
$`\sum_{\mathfrak{p}} N(\mathfrak{p})^{-2s}`$, which is bounded as
$`s \downarrow 1`$. Combining with $`\log \zeta_L(s) = -\log(s-1) + O(1)`$ from
the pole gives

$$\\mathrm{primeSum}(s) + \\log(s - 1) = O(1)
\\qquad (s \\downarrow 1)$$

(`FrobeniusDensity.primeSum_toReal_add_log_isBigO`, the 474-line analytic heart
of the subject). Feeding this through the decomposition of §5.1 and using the
tail bound yields the **degree-one asymptotic**

$$\\mathrm{degOneSum}(S_0, s) + \\log(s - 1) = O(1)
\\qquad (s \\downarrow 1)$$

(`FrobeniusDensity.degOneSum_add_log_isBigO`). In words: *the degree-one primes
alone already produce the full logarithmic divergence of the prime sum*, for every
finite exceptional set $`S_0`$. Together with summability of the individual terms
(`FrobeniusDensity.summable_degOne_term`), this is packaged, uniformly over
subgroups, as `FrobeniusDensity.DegOneAsymptotic` and realized unconditionally by
`FrobeniusDensity.degOneAsymptotic`.

## 6. From the analytic input to the density theorem

### 6.1 The statement

For a finite Galois $`L/\mathbb{Q}`$, the pin's `FrobeniusDensity.Statement L`
says: for every $`\sigma \in \mathrm{Gal}(L/\mathbb{Q})`$ and every finite set of
primes $`S`$, there is a prime $`\ell \notin S`$ such that at *every* prime
$`Q`$ of $`\mathcal{O}_L`$ over $`\ell`$ with finite residue field,

$$\\mathrm{Frob}_Q \\sim \\sigma^k
\\quad \\text{for some } k \\text{ with } (k, \\mathrm{order}\\,\\sigma) = 1.$$

The "for some $`k`$ coprime to the order" is the Möbius weight of §4; and since
$`\ell \notin S`$ is arbitrary, the set of such primes is infinite. This is the
**qualitative Frobenius density theorem**: the conjugacy class of the generators
of $`\langle \sigma \rangle`$ is realized by infinitely many primes, and hence
every nonempty conjugacy-stable subset of the group contains the Frobenius class
of a positive-density set of primes. (The pin proves the qualitative form, which
is what the applications need; the exact density $`|C|/|G|`$ is not required there.)

### 6.2 The proof: analysis plus Möbius inversion

`FrobeniusDensity.statement_of_degOneAsymptotic` deduces `Statement L` from
`DegOneAsymptotic L`. The argument is the classical one and uses exactly the pieces
above.

* Fix $`\sigma`$ and $`S`$. Let $`H = \langle \sigma \rangle`$ and let
  $`E = L^H`$ be its fixed field. The degree-one asymptotic applied to $`E`$
  (the quantification over subgroups in `DegOneAsymptotic`) says there are
  infinitely many degree-one primes of $`E`$ outside $`S`$; more precisely, it
  rules out the possibility that *all* degree-one primes of $`E`$ have Frobenius
  avoiding the class of $`\sigma`$. If they did, the corresponding Euler-type sum
  would be bounded, contradicting the $`\log(s-1)`$ divergence.
* §3.2 translates the count of degree-one primes of $`E`$ into a count of fixed
  points of the Frobenius on $`\mathrm{Gal}(L/\mathbb{Q})/H`$.
* §4's Möbius identity converts the fixed-point count into the count of $`g`$
  conjugating a generator $`\sigma^k`$ to $`\tau`$, and
  `ncard_conj_gen_ne_zero_iff` turns its non-vanishing into the conjugacy
  assertion of `Statement`.

So the density theorem is: *the pole of the Dedekind zeta function* (analysis)
$`+`$ *Möbius inversion on a finite group* (combinatorics). This is why the
subject is genuinely analytic at one end and representation-theoretic at the
other.

### 6.3 Globalization and density in an open subgroup

Two consequences are stated directly on $`\Gamma_{\mathbb{Q}}`$ rather than on a
finite group.

* `FrobeniusDensity.exists_frobenius_conj_pow_of_statement`: given `Statement` for
  all number fields, for a finite extension $`L/\mathbb{Q}`$ (no Galois hypothesis)
  and any $`\sigma \in \Gamma_{\mathbb{Q}}`$ and finite $`S`$, there is a prime
  $`\ell \notin S`$, a place $`A`$ over $`\ell`$, and an element
  $`\gamma \tau^j \gamma^{-1}`$ that agrees with $`\sigma`$ on all of $`L`$.
  The passage from the finite Galois level to $`\overline{\mathbb{Q}}`$ is the
  lifting lemma of §2.3; the point is that density inside
  $`\mathrm{Gal}(\text{Galois closure of }L/\mathbb{Q})`$ controls
  $`\sigma`$ on the possibly non-Galois $`L`$.

* `FrobeniusDensity.frobeniusPowerDense_of_le_ker`: for a finite Galois
  $`F/\mathbb{Q}`$ embedded in $`\overline{\mathbb{Q}}`$ and an open subgroup
  $`H \supseteq \ker(\Gamma_{\mathbb{Q}} \to \mathrm{Gal}(F/\mathbb{Q}))`$,
  the predicate `FrobeniusPowerDense S H` holds: for every
  $`\sigma \in \Gamma_{\mathbb{Q}}`$ there are $`\ell \notin S`$, a place
  $`A`$ over $`\ell`$, Frobenius $`\tau`$, and $`\gamma, j`$ with
  $`\gamma \tau^j \gamma^{-1} \sigma^{-1} \in H`$. In the finite quotient
  $`\Gamma_{\mathbb{Q}}/H`$, this says the Frobenius classes (and their powers
  and conjugates) meet every element: the Frobenius elements are **dense**, in the
  precise coset-wise sense the representation theory consumes, outside any finite
  set of primes.

* `Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen` is the version at
  the level of a single open subgroup: for any open $`H`$ and any prime bound
  $`M`$, there is a prime $`\ell \nmid M`$ with a Frobenius whose conjugate power
  lies in the coset $`\sigma H`$. This is the "open subgroup" form of density,
  equivalent to the statement that the map from Frobenius classes is onto the
  finite quotient.

## 7. The representation-theoretic consequences

### 7.1 A finite-image representation is determined by its Frobenius charpolys

> Let $`\rho, \rho' : \Gamma_{\mathbb{Q}} \to \mathrm{GL}_2(\mathbb{C})`$ have
> finite image. Suppose that for all primes $`p`$ outside a finite set, and all
> places $`A`$ over $`p`$ with Frobenius $`\sigma`$, the characteristic polynomials
> of $`\rho(\sigma)`$ and $`\rho'(\sigma)`$ agree. Then $`\rho`$ and $`\rho'`$
> are conjugate by a fixed $`P \in \mathrm{GL}_2(\mathbb{C})`$.

This is
`GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel`.
The two inputs are §6 and the finite-group theorem: a finite-image representation
factors through $`\mathrm{Gal}(F/\mathbb{Q})`$ for a common finite Galois $`F`$,
and the density theorem upgrades "agreement at almost all Frobenii" to "agreement
at every element of $`\mathrm{Gal}(F/\mathbb{Q})`$". For finite-dimensional
complex representations of a finite group, equality of characteristic polynomials
at every element implies conjugacy: the character $`\chi(g) = \mathrm{tr}\,\rho(g)`$
is the sum of the eigenvalues, all roots of unity, and the characteristic
polynomial of $`g`$ determines $`\chi(g)`$; a finite group representation is
determined by its character (Brauer–Nesbitt). The pin invokes the abstract finite
form `Representation.exists_conj_eq_of_charpoly_eq_of_finite_range`.

This is the lemma that makes "compatible system of residual representations"
meaningful: once the Frobenius charpolys are pinned down on a density-one set,
there is at most one finite-image $`\mathrm{GL}_2(\mathbb{C})`$-representation
with them.

### 7.2 Semisimple descent from Frobenius traces and determinants

> Let $`\kappa`$ be a finite field, $`\Omega`$ an algebraically closed field, and
> $`\iota : \kappa \hookrightarrow \Omega`$ an embedding. Let
> $`\rho : \Gamma_{\mathbb{Q}} \to \mathrm{GL}_2(\Omega)`$ have finite image, and
> suppose that at every prime outside a finite set the trace and determinant of
> $`\rho(\mathrm{Frob}_p)`$ lie in $`\iota(\kappa)`$. Then there is a finite-image
> representation $`\rho_0 : \Gamma_{\mathbb{Q}} \to \mathrm{GL}_2(\kappa)`$,
> with the same kernel as $`\rho`$, which is semisimple and whose characteristic
> polynomials map to those of $`\rho`$.

This is
`GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range`.
The mathematics is a two-character descent. In dimension two the characteristic
polynomial is determined by the trace and determinant, so suppose
$`\mathrm{tr}\,\rho = \chi_1 + \chi_2`$ and
$`\det\rho = \chi_1\chi_2`$ for two characters of a finite quotient. If
$`\chi_1`$ is not defined over $`\kappa`$ then its Galois twist
$`\chi_2 = \chi_1^{q}`$ is ($`q = |\kappa|`$), so the pair is a Frobenius orbit of
a single $`\kappa`$-valued character and the diagonal representation descends.
Either way the sum and product being $`\kappa`$-valued at all Frobenius elements —
and hence, by density, on the whole group — forces the representation to descend
and to be semisimple. In the Deligne–Serre application this is the step that
turns a representation with values in a large algebraically closed field into a
residual representation over the finite residue field, with the correct trace and
determinant.

### 7.3 Quantitative density

The final statement of the cluster is the *quantitative* half of Chebotarev used
for the order of the image.

Let $`\pi : \Gamma_{\mathbb{Q}} \twoheadrightarrow Q`$ be a surjection onto a
finite group $`Q`$ with finite level, and let $`C \subseteq Q`$ be stable under
conjugation. For every $`\delta \gt 0`$ there is $`s_0 \gt 1`$ such that for all
$`1 \lt s \lt s_0`$,

$$\\left(\\frac{|C|}{|Q|} - \\delta\\right)\\log\\frac{1}{s-1}
\\;\\le\\; \\sum_{p \\text{ prime}} p^{-s},$$

the sum over primes $`p`$ unramified in the quotient whose Frobenius class lies
in $`C`$.

This is `GaloisRep.sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective`. It
is the lower-bound direction of the Chebotarev density theorem with the expected
natural density $`|C|/|Q|`$: the primes with Frobenius in $`C`$ are numerous enough
to make their $`p^{-s}`$ sum diverge at least like
$`(|C|/|Q| - \delta)\log(1/(s-1))`$. The "for every $`\delta \gt 0`$" form is what
makes it usable without exact error terms: a positive-density Frobenius condition
produces, quantitatively, a definite number of primes. In the weight-one cone this
is the input to the bound on the order of the image of the residual representation
(`DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le`):
a lower bound on how often a Frobenius class occurs becomes an upper bound on how
large the image can be.

## 8. Where the pieces sit in Deligne–Serre

The forward weight-one theorem is an assembly of residual representations. Its
Frobenius-theoretic inputs are exactly three.

* **The data is on Frobenii.** The residual representations $`\rho_\ell`$ are
  constructed so that their characteristic polynomial at $`\mathrm{Frob}_p`$ is
  $`X^2 - \bar a_p X + \bar\varepsilon(p)`$, with the coefficients in a fixed
  finite ring. §2 supplies the meaning of the assertion and §2.3 lets the finite
  level data be read in $`\Gamma_{\mathbb{Q}}`$.
* **Almost all primes determine the object.** The gluing produces, for each
  residual prime, a representation over a finite field; the semisimple descent of
  §7.2 realizes it over the residue field, and the conjugacy criterion of §7.1
  identifies the resulting complex representation with the one attached to the
  form. Both are "density upgrades" of data known only at Frobenii.
* **Irreducibility and finite image.** The quantitative density of §7.3 bounds the
  order of the Frobenius image from below (enough primes in enough classes force
  the image to be large), which, combined with the Rankin-type bound that bounds
  it from above, confines the image to a finite set of possibilities; the limit is
  the Artin representation, and irreducibility follows from the cuspidality of the
  form. The determinant identity $`\det\rho = \varepsilon`$ and the oddness
  $`\varepsilon(-1) = -1`$ are the corresponding data at complex conjugation.

The subject is thus the **arithmetic glue** of the weight-one theorem: it does not
construct the residual representations (that is the lifting, and the Rankin/
coefficient-ring gates) and it does not prove the correspondence (that is the
converse and Langlands–Tunnell), but it is what allows the objects produced by
those halves to be *compared* prime by prime and then recognized as a single
Galois representation.

## 9. Lean inventory

Everything below is technical bookkeeping. The cluster under discussion is the
part of the weight-one cone belonging to this subject: **23 nodes**, measured
against the pin as 4,384 raw `S_` lines at the committed frontier. They split as

* **`FrobeniusDensity.*` — 18 nodes, 2,505 lines.** The analytic input, the
  counting identities, and the density theorem: `sum_moebius_mul_pos`,
  `weight_eq`, `ncard_conj_gen_ne_zero_iff`, `ncard_degreeOne_primesOver_under`,
  `ncard_degreeOne_primesOver_eq_ncard_frobFixed`,
  `stabilizer_eq_zpowers_arithFrobAt`, `idealSum_ne_top`,
  `tendsto_sub_one_mul_idealSum_test`, `summable_degOne_term`,
  `primeSum_eq_degOneSum_add`, `tailSum_le`, `primeSum_toReal_add_log_isBigO`,
  `degOneSum_add_log_isBigO`, `degOneAsymptotic`, `statement_of_degOneAsymptotic`,
  `statement`, `exists_frobenius_conj_pow_of_statement`,
  `frobeniusPowerDense_of_le_ker`.
* **`GaloisRep.*` — 3 nodes, 1,611 lines.** `exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel`,
  `exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range`,
  `sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective`.
* **Bridges — 2 nodes, 268 lines.**
  `NumberField.exists_isFrobenius_lift_arithFrobAt` (240) and
  `Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen` (28).

### 9.1 The definitions the statements are phrased with

New definition modules in the pin (all under `Definitions/`):

| module | contents | used by |
|---|---|---|
| `Def_TaylorWiles_Primes` | `ratPrimeIdeal` (line 42), `RealizesCyclicAt` (67), `Statement` (72), plus the `Matrix` trace/determinant identities | the density theorem and its consumers |
| `Def_FrobeniusDensity_DegOneAsymptotic` | `degOneCount` (22), `DegOneAsymptotic` (33) | the analytic input |
| `Def_FrobeniusDensity_PrimeSums` | `normRpow`, `idealSum`, `primeSum`, `primeSqSum`, `degOneSum`, `cutSum`, `tailSum`, `tailConst`, `idealCount`, `zetaTerm` | the analytic block |
| `Def_FrobeniusDensity_BadPrimes` | `badPrimes`, the finiteness of the ramified primes, `degOneCount_of_prime`, the `arithFrobAt` conjugacy lemmas | the "all but finitely many" bookkeeping |
| `Def_GaloisRep_FrobeniusPowerDense` | `FrobeniusPowerDense` (line 7) | §6.3 |
| `Def_GaloisRep_Residual` | `GaloisFactorsThroughFiniteLevel` (line 17) | §7.1, §7.2 |

The place vocabulary lives in older modules:
`Def_FLTPrelim_Ramification` (`LiesOverPrime` line 16, `inertiaSubgroupIn` line 21)
and `Def_EllipticCurve_FrobeniusTrace` (`IsFrobeniusAt` line 51). The pin also
needs `NumberField.exists_valuationSubring_eq_localization` and
`ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem` and the
`ValuationSubring` Frobenius family, which are stated in the same subject but are
counted as place/number-field vocabulary rather than as this cluster.

### 9.2 Shape of the proof graph

The `S_`/`Thm_` wrappers are thin; the mathematics is in the `S_` files (a public
`theorem solution` plus private helpers), and the `Thm_` files re-export it under
the pin's name by `p2m_exact_reverting`.

* `degOneAsymptotic` is a 16-line wrapper around the analytic block
  `degOneSum_add_log_isBigO` (292 lines) and `summable_degOne_term` (46), which
  themselves rest on `primeSum_toReal_add_log_isBigO` (474) and
  `primeSum_eq_degOneSum_add` (103)/`tailSum_le` (158).
* `statement_of_degOneAsymptotic` (165) is the combinatorial proof of §6.2;
  `statement` (12) composes it with `degOneAsymptotic`.
* `exists_frobenius_conj_pow_of_statement` (105) globalizes from a number field to
  $`\overline{\mathbb{Q}}`$ (§6.3), and `frobeniusPowerDense_of_le_ker` (47)
  repackages the result as density modulo an open subgroup.
* `GaloisRep.exists_isSemisimpleRepresentation_…` (495) delegates its proof to the
  private `DSRt.main` in the same file; the other two `GaloisRep.*` statements are
  171 and 945 lines.
* The Möbius prelude (`mem_zpowers_pow_div_iff`, `sum_moebius_mem_zpowers`,
  `exists_pow_coprime_eq_of_orderOf_eq`, `orderOf_pow_orderOf_div`,
  `ncard_conj_mem_eq_card_mul_ncard`, `ncard_eq_sum_indicator`) is repeated
  **verbatim and private** in both `sum_moebius_mul_pos` and `weight_eq`; the same
  `card_le_of_forall_pow_eq` occurs in `stabilizer_eq_zpowers_arithFrobAt` and
  `ncard_degreeOne_primesOver_under`. These are the dedup candidates of the
  subject.

### 9.3 What the pin takes from Mathlib

The heavy infrastructure is Mathlib's: `IsArithFrobAt`/`arithFrobAt` and the
decomposition/inertia groups (`Mathlib.RingTheory.Valuation.RamificationGroup`),
`Ideal.inertiaDeg`, the Dedekind zeta function and its residue
(`dedekindZeta`, `dedekindZeta_residue`,
`tendsto_sub_one_mul_dedekindZeta_nhdsGT`), the ideal-count asymptotics
(`Ideal.tendsto_norm_le_div_atTop₀`,
`card_norm_le_eq_card_norm_le_add_one`), `LSeriesSummable_of_sum_norm_bigO_and_nonneg`,
and `MulAction.stabilizer`/quotient-group cardinalities. What the pin proves is
the *comparison* of the prime sum with $`\log\zeta`$, the degree-one extraction,
and the Möbius/Chebotarev combinatorics — precisely the parts not packaged as a
named theorem in Mathlib.
