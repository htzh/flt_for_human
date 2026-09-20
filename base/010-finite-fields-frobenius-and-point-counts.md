# Finite fields, Frobenius, and point counts

Tenth of the `base/` notes. [007](007-weil-pairing.md) covered torsion and the
Weil pairing, [008](008-divisors-and-pic0.md) divisors and
$`\mathrm{Pic}^0`$ with the rank-$`2g`$ count, and
[009](009-differentials-residues-riemann-roch.md) differentials and
Riemann–Roch. This note is the arithmetic of a curve over a **finite field**:
the Frobenius endomorphism, its characteristic polynomial, Hasse's bound, the
counts of points over extensions of the base field, and the free rank-$`2`$
(rank-$`2g`$) Tate module. It is the mathematics behind
`pymath/frobenius_charpoly.py` and behind three anchors in the code:
`FrobCharEqOnPoints` (the characteristic equation), `galoisTrace` (the trace on
$`E[n]`$), and `ResidualGaloisRep.IsAttachedTo` (where this polynomial becomes
the bridge from an elliptic curve to a modular form).

Math first: §§1–5 are the theory, §6 is the computation carried out in the
demo, and §7 summarizes how the code encodes it. Nothing here is
characteristic-free in the way [009](009-differentials-residues-riemann-roch.md)
was: the whole subject is what happens over $`\mathbb{F}_q`$, and the one place
the characteristic bites is $`p`$-torsion, which §4 flags.

Line-number citations point at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib
citations point at tag **v4.33.0**. Both are rendered GitHub links.

## 1. A curve over a finite field

Let $`q = p^n`$ and let $`C`$ be a curve over $`\mathbb{F}_q`$, with function
field $`F = \mathbb{F}_q(C)`$. Two features of the finite world organize
everything below.

**The fields are perfect.** Every finite field is perfect — the Frobenius
$`x \mapsto x^p`$ is injective, hence bijective, on a finite field — so the
separability caveats of [009 §1](009-differentials-residues-riemann-roch.md)
are automatically met: differentials, orders, the canonical divisor and the
genus behave exactly as over $`\bar{\mathbb{Q}}`$.

**Rational points are fixed points.** The $`q`$-power map acts on the points
over an algebraic closure, and the points defined over $`\mathbb{F}_q`$ are
precisely the ones it fixes:

$$C(\mathbb{F}_q) \\;=\\; \\{\\, P \in C(\bar{\mathbb{F}}_q) :
  \varphi_q(P) = P \\,\\},$$

where $`\varphi_q`$ raises coordinates to the $`q`$-th power. On a plane model
$`E : y^2 = x^3 + ax + b`$ this says: $`(x,y)`$ is rational exactly when
$`x^q = x`$ and $`y^q = y`$. Counting points therefore becomes a question about
the *fixed locus of one endomorphism* — which is §2.

For a finite field $`E(\mathbb{F}_q)`$ is a finite abelian group, and it is
known to be a product of at most two cyclic groups, say
$`\mathbb{Z}/n_1 \times \mathbb{Z}/n_2`$ with $`n_1 \mid n_2`$. The torsion
theorem of [math/005](../math/005-card-torsion-p-squared.md) is the input for
that structure, and §4 uses it to identify $`E[n]`$ as a free rank-$`2`$ module.

## 2. The Frobenius endomorphism

Write $`\varphi_q`$ as a map of the curve itself, with $`\varphi_q(O) = O`$:

$$\varphi_q \\;:\\; E \longrightarrow E, \qquad
  (x, y) \longmapsto (x^q, y^q).$$

It is an **endomorphism**. The addition laws on a Weierstrass model have
coefficients in $`\mathbb{F}_q`$, and $`a^q = a`$ for $`a \in \mathbb{F}_q`$,
so the group law is carried to itself; equivalently, $`x \mapsto x^q`$ is a field
endomorphism of $`\mathbb{F}_q(E)`$ fixing $`\mathbb{F}_q`$ and commuting with
the group structure.

**Isogenies, degree, and separability.** An *isogeny* $`\alpha : E \to E'`$ is a
surjective morphism of curves with $`\alpha(O) = O`$; it is automatically a group
homomorphism. Its **degree** is the degree of the pullback of function fields,

$$\deg \alpha \\;=\\; [\\,K(E) : \alpha^{\ast}K(E')\\,],$$

The extension here is the *source's* function field: $`\alpha`$ pulls functions
back, so $`K(E')`$ embeds in $`K(E)`$ and it is $`K(E)`$ that grows. The lattice
model matches the index. Write $`E = \mathbb{C}/\Lambda`$ and
$`E' = \mathbb{C}/\Lambda'`$; then $`\alpha`$ is induced by a scalar $`\lambda`$
with $`\lambda\Lambda \subseteq \Lambda'`$, so after rescaling $`\lambda = 1`$
the source lattice is the sublattice, the degree is $`[\Lambda' : \Lambda]`$, and
the kernel is $`\Lambda'/\Lambda`$ — a smaller lattice imposes fewer periodicity
conditions, hence carries the larger function field. The dual isogeny has the
same degree and reverses the direction, so which of the two lattices one calls
"the sublattice" is a matter of which map is in hand.

The **degree** equals the number of points in the kernel over $`\bar{K}`$ exactly when
$`\alpha`$ is **separable** — then the kernel is a finite group of order
$`\deg \alpha`$. If instead the field extension is *purely inseparable* — every
element of $`K(E)`$ has its $`p`$-th power in $`\alpha^*K(E')`$ — then the kernel
has no non-identity points at all, and the degree is invisible to a point count.

Two numerical facts about $`\varphi_q`$ now matter:

- it is **purely inseparable of degree $`q`$**: $`K(E)`$ is generated over
  $`\varphi_q^*K(E) = K(E)^q`$ by $`x`$ and $`y`$, whose $`q`$-th powers lie in
  that subfield, and the extension has degree $`q`$ — one dimension of
  transcendence degree, not two, because $`x`$ and $`y`$ are tied by the
  Weierstrass equation. So $`\deg \varphi_q = q`$, while $`\ker \varphi_q`$ has
  only $`O`$ as a point: the number $`q`$ is the *degree* here, not a kernel
  count;
- its **separable companion** $`\varphi_q - 1`$ is separable, and its kernel is
  exactly the rational points:

$$\\# E(\mathbb{F}_q) \\;=\\; \deg(\varphi_q - 1).$$

That identity is the bridge from algebra to counting: point counts become
degrees of isogenies. The endomorphism $`\varphi_q - 1`$ is separable of degree
$`\#E(\mathbb{F}_q)`$, and every rational point is in its kernel, so the kernel
and the count agree.

Frobenius also sits in the centre of $`\mathrm{End}(E)`$: it commutes with every
endomorphism, because it already commutes with the group law. That is what lets
it be treated as a scalar-like element — in particular, as an algebraic integer
satisfying a quadratic equation, §3.

## 3. The characteristic polynomial, and Hasse's bound

The central theorem of the subject is that $`\varphi_q`$ satisfies a quadratic
equation with integer coefficients:

$$\varphi_q^{\\,2} - a_q\\,\varphi_q + q \\;=\\; 0,
  \qquad a_q \\;=\\; q + 1 - \\#E(\mathbb{F}_q).$$

So the **characteristic polynomial of Frobenius** is

$$T^2 - a_q\\,T + q,$$

with trace $`a_q`$ and determinant $`q`$. Neither coefficient is an accident:

- the determinant $`q`$ is $`\deg \varphi_q`$, and it is also the statement that
  the Weil pairing is multiplied by $`q`$ under Frobenius — the identity
  $`e_n(\varphi_q P, \varphi_q Q) = e_n(P,Q)^q`$ of
  [007 §2](007-weil-pairing.md), which is why no separate hypothesis is needed;
- the trace $`a_q`$ is, by the equation itself,
  $`a_q = q + 1 - \#E(\mathbb{F}_q)`$, so the polynomial *computes* the point
  count: $`\#E(\mathbb{F}_q) = q + 1 - a_q`$.

**Hasse's bound** constrains the trace,

$$|a_q| \\;\le\\; 2\sqrt{q}, \qquad\text{equivalently}\qquad a_q^2 \le 4q,$$

and says exactly that the two roots $`\alpha, \beta`$ of the polynomial have
modulus $`\sqrt{q}`$:

$$\alpha + \beta = a_q, \qquad \alpha\beta = q, \qquad
  |\alpha| = |\beta| = \sqrt{q}.$$

The roots are Galois-conjugate complex numbers (or $`\ell`$-adic ones); their
modulus is the form of Hasse's bound that generalizes to curves of higher genus.

**Counts over extensions.** Since $`\varphi_q^k = \varphi_{q^k}`$, the same
polynomial controls every extension field. The traces satisfy the linear
recurrence $`a_{q^k} = a_q\,a_{q^{k-1}} - q\,a_{q^{k-2}}`$, and

$$\\#E(\mathbb{F}_{q^k}) \\;=\\; q^k + 1 - a_{q^k}
  \\;=\\; q^k + 1 - \bigl(\alpha^k + \beta^k\bigr).$$

One degree-two polynomial of integers therefore determines the point count over
*every* finite extension of $`\mathbb{F}_q`$ — the fact §6 watches against brute
force. It is also the arithmetic shadow of the Lefschetz trace formula, with the
two roots playing the role of the two eigenvalues of Frobenius on $`H^1`$.

## 4. Torsion, and the Tate module

Let $`n`$ be coprime to $`p`$. The torsion theorem
([math/005](../math/005-card-torsion-p-squared.md)) gives

$$\\# E[n]\bigl(\bar{\mathbb{F}}_q\bigr) \\;=\\; n^2,
  \qquad E[n] \\;\cong\\; (\mathbb{Z}/n)^2,$$

the second statement being the group structure that comes with the first: a
finite abelian group with $`n^2`$ elements killed by $`n`$ is a free
$`\mathbb{Z}/n`$-module of rank $`2`$. The coprimality of $`n`$ and $`p`$ is
essential: for $`n`$ divisible by $`p`$ the statement fails, $`E[p]`$ being a
group scheme of order $`p^2`$ that may be connected rather than $`(\mathbb{Z}/p)^2`$
(it is étale of that form only for ordinary curves, and even then only as a
group scheme). Everything below assumes $`n`$ coprime to $`p`$, as does the
demo.

Frobenius acts on $`E[n]`$ and, in any basis, is a $`2 \times 2`$ matrix over
$`\mathbb{Z}/n`$ whose characteristic polynomial is the reduction of §3:

$$\mathrm{tr}\varphi_q = a_q \bmod n, \qquad
  \det\varphi_q = q \bmod n, \qquad
  M^2 - a_q\\,M + q \\;=\\; 0 \quad \text{on } E[n].$$

Passing to the inverse limit over $`n = \ell^k`$, the **$`\ell`$-adic Tate
module**

$$T_\ell E \\;=\\; \varprojlim_k E[\ell^k]$$

is a free $`\mathbb{Z}_\ell`$-module of rank $`2`$ on which the absolute Galois
group acts, with Frobenius acting by a matrix of characteristic polynomial
$`T^2 - a_qT + q`$. For a curve of genus $`g`$ the same construction on the
Jacobian gives the rank-$`2g`$ statement that
[008 §4](008-divisors-and-pic0.md) states as a cardinality count and
[009 §3](009-differentials-residues-riemann-roch.md) as the genus:

$$T_\ell J(C) \\;\cong\\; \mathbb{Z}_\ell^{2g},
  \qquad\text{since } \\#J(C)[\ell^k] = \ell^{2gk}.$$

## 5. Why FLT needs all this

Three uses, in increasing specificity.

**The characteristic polynomial is the bridge to modular forms.** For the Frey
curve, the Galois representation on $`E[\ell]`$ is attached to a cusp form when
the characteristic polynomial of $`\rho(\mathrm{Frob}_\ell)`$ matches the Hecke
eigenvalue: this is literally the statement `ResidualGaloisRep.IsAttachedTo`
(§7), whose conclusion is
$`\mathrm{charpoly}(\rho(\sigma)) = X^2 - \varphi(a)X + \ell`$ with
$`(a : \mathbb{C})`$ the $`\ell`$-th $`q`$-coefficient of the form. So the point
counts of §3 are what a modular form is compared against.

**The determinant is the cyclotomic character.** The constant term $`\ell`$ of
the polynomial is the determinant of $`\rho(\mathrm{Frob}_\ell)`$, i.e. the
value of the cyclotomic character — [007 §2](007-weil-pairing.md) derives
$`\det \rho = \chi_\ell`$ from the Weil pairing, and $`\chi_\ell(c) = -1`$ for
complex conjugation is the *oddness* of the representation.

**The rank-$`2g`$ Tate module carries the Hecke action.** The modularity and
level-lowering steps are statements about the Galois module $`T_\ell J_0(N)`$,
which has rank $`2g`$ with $`g`$ the genus of $`X_0(N)`$ computed in
[009 §7](009-differentials-residues-riemann-roch.md), and on which the Hecke
operators act ([math/009](../math/009-hecke-jacobian-commute.md)). The elliptic
case of §4 is the same statement with $`g = 1`$, and it is the one the demo
checks.

**Separability is a matter of characteristic.** The distinction of §2 has a
characteristic-dependent shape that is easy to misplace. A degree-$`p`$ map whose
local form is $`t \mapsto t^p`$ is *purely inseparable* over a field of
characteristic $`p`$ — that is §2's Frobenius — but *separable* over a field of
characteristic $`0`$. So the covering of
[005](005-cyclic-isogenies-and-level.md) and
[006](006-the-modular-equation.md), whose local form at the cusps is the nome
substitution $`q = q'^p`$ with ramification index $`p`$, is separable throughout:
over $`\mathbb{Q}`$ it is a degree-$`p+1`$ map with $`p+1`$ distinct sheets, which
is why the modular equation has that many roots. The inseparable version of the
very same substitution lives in characteristic $`p`$, on the reduction of the
modular curve: the `CharLFrobenius*` declarations of
[011 §6](011-deformations-hecke-algebras-and-r-equals-t.md).

## 6. The computation: `pymath/frobenius_charpoly.py`

The demo works over small prime fields and their extensions, so that every
number can be checked twice — once from the polynomial and once by brute force.
Its output
[`../pymath/frobenius_charpoly.expected.txt`](../pymath/frobenius_charpoly.expected.txt)
is written as an explanation, and its $`9`$ `check` lines are §3 and §4
evaluated.

- **The polynomial and Hasse.** It records
  $`\pi^2 - a_q\pi + q = 0`$ with $`a_q = q + 1 - \#E(\mathbb{F}_q)`$, the
  polynomial $`T^2 - a_qT + q`$ with trace $`a_q`$ and determinant $`q`$, and
  Hasse's bound in the form $`a_q^2 \le 4q`$. The determinant is identified with
  the Weil-pairing statement of [007 §2](007-weil-pairing.md), exactly as in §3.
- **Point counts.** For several curves over $`\mathbb{F}_5`$, $`\mathbb{F}_7`$,
  $`\mathbb{F}_{11}`$ and $`\mathbb{F}_{41}`$ it tabulates $`\#E`$, the trace
  $`a_q`$, $`a_q^2`$ and $`4q`$, and checks Hasse on every row. Two of the rows
  are curves already met in this series: $`y^2 = x^3 - x`$ over
  $`\mathbb{F}_7`$ with $`\#E = 8`$ and $`a_q = 0`$ (the curve of
  [008 §6](008-divisors-and-pic0.md)), and $`y^2 = x^3 + 2`$ over
  $`\mathbb{F}_7`$ with $`\#E = 9`$ (the curve of
  [math/005 §6](../math/005-card-torsion-p-squared.md)).
- **Counts over extensions.** Using the recurrence
  $`a_{q^k} = a_qa_{q^{k-1}} - qa_{q^{k-2}}`$, it predicts
  $`\#E(\mathbb{F}_{q^k}) = q^k + 1 - a_{q^k}`$ and compares with a brute-force
  count over $`\mathbb{F}_{q^2}`$ and $`\mathbb{F}_{q^3}`$ — the check that one
  quadratic polynomial knows all the extensions.
- **The roots.** It factors the polynomial over $`\mathbb{C}`$ for several
  traces and verifies $`\alpha + \beta = a_q`$, $`\alpha\beta = q`$ and
  $`|\alpha|^2 = q`$ — Hasse's bound in modulus form.
- **Frobenius on $`E[n]`$.** It exhibits $`E[n]`$ as free of rank $`2`$
  ($`\#E[2] = 4`$ and $`\#E[3] = 9`$ for two curves over $`\mathbb{F}_7`$) and,
  over $`\mathbb{F}_{25}`$ where the $`3`$-torsion becomes rational, computes
  the Frobenius matrix of $`y^2 = x^3 + 1`$ over $`\mathbb{F}_5`$:
  $`[[1,0],[0,2]]`$ mod $`3`$, with trace $`0 = a_5 \bmod 3`$ and determinant
  $`2 = 5 \bmod 3`$, and checks $`M^2 - a_qM + q = 0`$.

The demo's own §6 is the one that names the formalization: the characteristic
polynomial is the link between a Galois representation and a modular form, and
the rank statement is the rank-$`2g`$ theorem of §7.

## 7. How the code says all this

**Finite fields.** Mathlib's finite structures are
$`\mathbb{Z}/n`$ and its splitting-field model of $`\mathbb{F}_{p^n}`$:

```lean
def ZMod : ℕ → Type
```
```lean
theorem card (n : ℕ) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
```
```lean
def GaloisField := SplittingField (X ^ p ^ n - X : (ZMod p)[X])
```

([Data/ZMod/Defs.lean, lines 142 and 166](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Data/ZMod/Defs.lean#L142-L166),
[FieldTheory/Finite/GaloisField.lean, line 69](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Finite/GaloisField.lean#L69)).
The first two are what the project uses for torsion: $`E[n]`$ is a
$`\mathbb{Z}/n`$-module and the cardinality is `Nat.card`. `GaloisField` is
mathlib's $`\mathbb{F}_{p^n}`$ — the splitting field of $`X^{p^n} - X`$, which is
one way to say "the field whose elements are the fixed points of
$`\varphi_{p^n}`$", i.e. §1's characterization turned into a definition. The
demo implements its own $`\mathbb{F}_{p^n}`$ arithmetic rather than using this,
so that the counts are independent of the library.

**The Frobenius endomorphism and its equation.** The endomorphism is
`frobEnd`, and the quadratic equation of §3 is a property of point groups:

```lean
abbrev frobEnd : (W⁄k).Point →+ (W⁄k).Point :=
```
```lean
def FrobCharEqOnPoints (a : ℤ) (q : ℕ) : Prop :=
```

([Def_EllipticCurve_FrobeniusEndo.lean, lines 39 and 50](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusEndo.lean#L39-L50)).
Note the encoding: the equation is a `Prop` about the point group, not an
identity in `End(E)`. The file's companions `linePencil` and `kerDeg`
([lines 14 and 21](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusEndo.lean#L14-L21))
are the proof device: the kernel degree of the pencil
$`\varphi_q - m - n`$, which is how $`\deg(\varphi_q - 1) = \#E(\mathbb{F}_q)`$
and the quadratic equation are attacked without leaving the point group.

**The trace on torsion.** For $`E[n]`$ the trace of a Galois element is an
element of $`\mathbb{Z}/n`$:

```lean
def galoisRepModuleEnd (W' : Affine R) (n : ℕ) :
```
```lean
def galoisTrace (W' : Affine R) (n : ℕ) (σ : K ≃ₐ[S] K) : ZMod n
```

([Def_EllipticCurve_FrobeniusTrace.lean, lines 25 and 36](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusTrace.lean#L25-L36)),
with the arithmetic-Frobenius predicate

```lean
def IsFrobeniusAt (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q : ℕ) : Prop :=
```

([line 51](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusTrace.lean#L51)).
This is §4's $`\mathrm{tr}\varphi_q = a_q \bmod n`$: the trace lands in
$`\mathbb{Z}/n`$, which is exactly where it can be compared with a point count
reduced modulo $`n`$.

**The Tate module and its rank.** The rational Tate module is a base change of
the integral one:

```lean
abbrev RationalTateModule : Type :=
  ℚ_[p] ⊗[ℤ_[p]] TateModule p J
```

([Def_ModularCurve_JZeroTateModule.lean, line 45](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_JZeroTateModule.lean#L45)),
with the Galois representation `rationalGaloisRep`
([line 48](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_JZeroTateModule.lean#L48)),
and §4's rank statement is

`Pic0.finrank_rationalTateModule_eq_two_mul_genusFF_of_charZero`
([Thm file, line 18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Pic0_finrank_rationalTateModule_eq_two_mul_genusFF_of_charZero.lean#L18)):
$`\mathrm{finrank}_{\mathbb{Q}_\ell}\bigl(\mathrm{RationalTateModule}\ \ell\
(\mathrm{Pic}^0)\bigr) = 2\cdot\mathrm{genusFF}`$
([line 22](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Pic0_finrank_rationalTateModule_eq_two_mul_genusFF_of_charZero.lean#L22)).
The genus here is the one defined in
[009 §1](009-differentials-residues-riemann-roch.md) from the canonical divisor.

**The torsion input and the modularity anchor.** The rank-$`2`$ fact for
$`E[n]`$ is the torsion theorem of
[math/005](../math/005-card-torsion-p-squared.md)
(`WeierstrassCurve.card_torsion_of_isAlgClosed`,
`nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed`,
`finrank_zmod_torsionBy_point_eq_two`), and the modularity statement of §5 is

```lean
def IsAttachedTo (ρ : ResidualGaloisRep k) {N : ℕ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (φ : integralClosure ℤ ℂ →+* k) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → (ℓ : k) ≠ 0 →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
        ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (φ a) * X + C ((ℓ : k))
```

([Def_GaloisRep_Residual.lean, lines 48–56](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean#L48-L56)):
at every good prime $`\ell`$, the characteristic polynomial of
$`\rho(\sigma)`$ for a Frobenius $`\sigma`$ is $`X^2 - aX + \ell`$ with $`a`$ the
$`\ell`$-th $`q`$-coefficient of the form. The neighbouring definitions are
`IsUnramifiedAt` ([line 43](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean#L43))
and, for the determinant side of §5, `IsOdd`
([line 58](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean#L58)).
Finally, the Frobenius action on $`\mathrm{Pic}^0`$ that the Hecke comparison
runs on is `frobeniusPullbackGeomLevelPic0` and
`frobeniusPushforwardGeomLevelPic0`
([Def_ModularCurve_CharLFrobeniusGeomLevel.lean, lines 1344 and 1360](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_CharLFrobeniusGeomLevel.lean#L1344-L1360)),
with the divisor-level and $`\mathrm{Pic}^0`$-level endomorphisms in
[Def_AlgebraicCurve_FrobeniusEndo.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_FrobeniusEndo.lean)
and
[Def_AlgebraicCurve_FrobeniusEndoPic0.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_FrobeniusEndoPic0.lean)
— the neighbours that [008 §8](008-divisors-and-pic0.md) lists.

### Key point → declaration map

| Mathematics | Lean declaration | Location |
|---|---|---|
| $`\mathbb{Z}/n`$ as a finite ring, its cardinality | `ZMod`, `ZMod.card` | [Data/ZMod/Defs.lean 142, 166](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Data/ZMod/Defs.lean#L142-L166) |
| $`\mathbb{F}_{p^n}`$ as the splitting field of $`X^{p^n} - X`$ | `GaloisField` | [FieldTheory/Finite/GaloisField.lean 69](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Finite/GaloisField.lean#L69) |
| the Frobenius endomorphism on points | `frobEnd` | [FrobeniusEndo 39](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusEndo.lean#L39) |
| the characteristic equation $`\varphi_q^2 - a_q\varphi_q + q = 0`$ | `FrobCharEqOnPoints` | [50](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusEndo.lean#L50) |
| kernel degree of the pencil $`\varphi_q - m - n`$ | `linePencil`, `kerDeg` | [14](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusEndo.lean#L14), [21](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusEndo.lean#L21) |
| the trace on $`E[n]`$, as an element of $`\mathbb{Z}/n`$ | `galoisTrace`, `galoisRepModuleEnd` | [FrobeniusTrace 25, 36](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusTrace.lean#L25-L36) |
| "$`\sigma`$ is a Frobenius at $`q`$" | `IsFrobeniusAt` | [51](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusTrace.lean#L51) |
| the rational Tate module, and its Galois action | `RationalTateModule`, `rationalGaloisRep` | [JZeroTateModule 45, 48](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_JZeroTateModule.lean#L45-L48) |
| rank $`2g`$ | `Pic0.finrank_rationalTateModule_eq_two_mul_genusFF_of_charZero` | [Thm 18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Pic0_finrank_rationalTateModule_eq_two_mul_genusFF_of_charZero.lean#L18) |
| $`\#E[n] = n^2`$ and $`E[n] \cong (\mathbb{Z}/n)^2`$ | `card_torsion_of_isAlgClosed`, `nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed` | [math/005 §1](../math/005-card-torsion-p-squared.md) |
| Frobenius on divisors and on $`\mathrm{Pic}^0`$ | `frobeniusPullbackGeomLevelPic0`, `frobeniusPushforwardGeomLevelPic0` | [CharLFrobeniusGeomLevel 1344, 1360](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_CharLFrobeniusGeomLevel.lean#L1344-L1360) |
| the modularity link: char poly $`= X^2 - a_\ell X + \ell`$ | `ResidualGaloisRep.IsAttachedTo` | [GaloisRep_Residual 48–56](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean#L48-L56) |
| oddness of the representation | `ResidualGaloisRep.IsOdd` | [58](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean#L58) |

## 8. Links

FLT sources at the pinned sha `aa2d8b3`:

- [Def_EllipticCurve_FrobeniusEndo.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusEndo.lean) — `frobEnd`, `FrobCharEqOnPoints`, `linePencil`, `kerDeg`
- [Def_EllipticCurve_FrobeniusTrace.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusTrace.lean) — `galoisRepModuleEnd`, `galoisTrace`, `IsFrobeniusAt`
- [Def_ModularCurve_JZeroTateModule.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_JZeroTateModule.lean) — `TateModule`, `RationalTateModule`, `rationalGaloisRep`
- [Thm_AlgebraicCurve_Pic0_finrank_rationalTateModule_eq_two_mul_genusFF_of_charZero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Pic0_finrank_rationalTateModule_eq_two_mul_genusFF_of_charZero.lean) — rank $`2g`$
- [Def_GaloisRep_Residual.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean) — `IsAttachedTo`, `IsUnramifiedAt`, `IsOdd`
- [Def_AlgebraicCurve_FrobeniusEndo.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_FrobeniusEndo.lean) and [Def_AlgebraicCurve_FrobeniusEndoPic0.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_FrobeniusEndoPic0.lean) — Frobenius on divisors and on $`\mathrm{Pic}^0`$

Mathlib at tag `v4.33.0`:

- [Data/ZMod/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Data/ZMod/Defs.lean) — `ZMod` and its cardinality
- [RingTheory/Finite/GaloisField.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Finite/GaloisField.lean) — `GaloisField`
- [Algebra/Module/ZMod.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/ZMod.lean) — the $`\mathbb{Z}/n`$-module structure

Demos at the same revision:

- [pymath/frobenius_charpoly.py](../pymath/frobenius_charpoly.py) — the computation of §6, and its [golden output](../pymath/frobenius_charpoly.expected.txt)
- [pymath/weil_pairing.py](../pymath/weil_pairing.py) — the pairing and the finite-field torsion examples of [007](007-weil-pairing.md)
- [pymath/README.md](../pymath/README.md) — the demo index

Companion notes:

- [007 — The Weil pairing](007-weil-pairing.md) — the pairing, its behaviour under Frobenius, and the Tate module
- [008 — Divisors, linear equivalence, and Pic⁰](008-divisors-and-pic0.md) — $`\mathrm{Pic}^0`$, the rank-$`2g`$ count, and the curve $`y^2 = x^3 - x`$ over $`\mathbb{F}_7`$
- [009 — Differentials, residues, and Riemann–Roch](009-differentials-residues-riemann-roch.md) — why finite fields are perfect, and the genus
- [math/005](../math/005-card-torsion-p-squared.md) — $`\#E[n] = n^2`$ and the free rank-$`2`$ module, with its finite-field section
