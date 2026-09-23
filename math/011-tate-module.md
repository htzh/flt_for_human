# The Tate module, and the Galois representations attached to elliptic curves and modular forms

Companion to [note 005](005-card-torsion-p-squared.md) ($`\#E[n] = n^2`$, the
input that makes the Tate module free of rank two), [note 003](003-galois-rep-irreducible-in-english.md)
(the irreducibility predicate), [note 004](004-irreducible-and-cofixed-line.md)
(the cofixed-line detour), [base/007](../base/007-weil-pairing.md) (the Weil
pairing, which produces $`\det\rho = \chi`$), [base/014](../base/014-hecke-operators.md)
(Hecke operators) and [math/009](009-hecke-jacobian-commute.md) (the Jacobian
$`J_0(N)`$ and the Hecke action on it).

This note is about the mathematics. The previous notes established that
$`E[p](\bar K)`$ is a two-dimensional $`\mathbb{F}_p`$-vector space; the Tate
module is the next step, the compatible system of all $`p`$-power torsion and its
limit. On the automorphic side the same construction, applied to the Jacobian
$`J_0(N)`$ instead of an elliptic curve, attaches a Galois representation to a
weight-two eigenform — this is Eichler–Shimura. The two constructions are the
objects the whole FLT argument reasons about: irreducibility, modularity,
residual modularity and level lowering are all statements about these
representations.

The Lean formalization appears in §5 and in the key-point map of §6; the
narrative does not depend on it. Line numbers refer to
`anthropics/fermats-last-theorem@aa2d8b3` (main, 2026-09-03); Mathlib line
numbers refer to tag `v4.33.0`.

## 1. The Tate module of an elliptic curve

### 1.1 The inverse system $`E[p^n]`$

Let $`E`$ be an elliptic curve over a field $`K`$ and $`p`$ a prime with
$`\mathrm{char}\,K \nmid p`$. Multiplication by $`p`$,
$$[p] : E(\bar K) \longrightarrow E(\bar K),$$
maps $`E[p^{n+1}]`$ onto $`E[p^n]`$, so the $`p`$-power torsion groups form an
inverse system
$$E[p] \xleftarrow{[p]} E[p^2] \xleftarrow{[p]} E[p^3] \xleftarrow{[p]} \cdots .$$
The Tate module is its inverse limit:
$$T_p E \\;=\\; \varprojlim_{n}\\, E[p^n](\bar K).$$

Concretely, an element of $`T_pE`$ is a sequence $`(P_n)_{n \ge 1}`$ with
$`P_n \in E[p^n](\bar K)`$ and $`[p]P_{n+1} = P_n`$ for every $`n`$. The group law
is coordinatewise, and $`T_pE`$ is an abelian group. It carries a
$`\mathbb{Z}_p`$-module structure: the scalar $`a \in \mathbb{Z}_p`$ acts on
$`(P_n)`$ by $`a \cdot (P_n) = (a_n P_n)`$ where $`a_n`$ is the image of $`a`$ in
$`\mathbb{Z}/p^n`$; the compatibility $`[p]P_{n+1} = P_n`$ is exactly what makes
this well defined. One also sets
$$V_p E \\;=\\; T_p E \otimes_{\mathbb{Z}_p} \mathbb{Q}_p .$$

### 1.2 Rank two

Let the base be algebraically closed, so that $`\#E[p^n] = (p^n)^2`$ for every
$`n`$ (the theorem of [note 005](005-card-torsion-p-squared.md), from which the
general case follows by base change). Two consequences are the reason the Tate
module is the right object.

* **The limit is free of rank two.** For each $`n`$ the reduction map
  $`T_pE \to E[p^n]`$ is surjective with kernel $`p^n T_pE`$, so
  $$T_pE / p^n T_pE \\;\cong\\; E[p^n].$$
  In particular $`T_pE/pT_pE \cong E[p]`$ has order $`p^2`$. The limit is
  torsion-free: if $`p x = 0`$ then $`x_n = p x_{n+1} = 0`$ for every $`n`$, so
  $`x = 0`$. A torsion-free $`\mathbb{Z}_p`$-module whose reduction mod $`p`$ has
  order $`p^2`$ is free of rank two — Nakayama gives two generators, and
  torsion-freeness over the discrete valuation ring $`\mathbb{Z}_p`$ makes a
  finitely generated module free. So
  $$T_pE \\;\cong\\; \mathbb{Z}_p^{\\,2}, \qquad
    V_pE \\;\cong\\; \mathbb{Q}_p^{\\,2}.$$
* **The integral structure remembers the residual representation.** The natural
  map $`T_pE \to T_pE/pT_pE`$ identifies $`E[p]`$ with
  $`T_pE \otimes_{\mathbb{Z}_p} \mathbb{F}_p`$. Choosing a
  $`\mathbb{Z}_p`$-basis of $`T_pE`$ therefore gives compatible bases of every
  $`E[p^n]`$, and reduces the mod-$`p`$ representation to a
  $`2\times 2`$ matrix over $`\mathbb{F}_p`$.

### 1.3 Why this is the right integral object

Because $`T_pE`$ is free, every $`\mathbb{Z}_p`$-linear endomorphism has a
determinant and a characteristic polynomial in $`\mathbb{Z}_p`$, and these reduce
mod $`p`$. That is what lets the proof compare a $`p`$-adic representation with
its mod-$`p`$ shadow level by level, and it is why the compatibility of the
torsion groups — not just $`E[p]`$ — is needed.

## 2. The Galois action

### 2.1 The action on torsion points

Let $`G_K = \mathrm{Gal}(\bar K/K)`$ and let $`E`$ be defined over $`K`$. Because
the group law of $`E`$ is given by rational functions with coefficients in
$`K`$, every $`\sigma \in G_K`$ acts on $`E(\bar K)`$ by applying $`\sigma`$ to
the coordinates:
$$\sigma \cdot P \\;=\\; (\sigma x, \sigma y) \quad \text{for } P=(x,y).$$
This action commutes with every endomorphism of $`E`$ that is defined over $`K`$,
in particular with $`[p]`$. Hence it preserves each $`E[p^n]`$ and commutes with
the transition maps, so it passes to the limit:
$$\rho_{E,p} : G_K \longrightarrow \mathrm{Aut}_{\mathbb{Z}_p}(T_pE).$$
Choosing a $`\mathbb{Z}_p`$-basis identifies
$`\mathrm{Aut}_{\mathbb{Z}_p}(T_pE) \cong \mathrm{GL}_2(\mathbb{Z}_p)`$ and gives
the Galois representation attached to $`E`$:
$$\rho_{E,p} : G_K \to \mathrm{GL}_2(\mathbb{Z}_p).$$
Composing with the reduction $`\mathrm{GL}_2(\mathbb{Z}_p) \to \mathrm{GL}_2(\mathbb{F}_p)`$
gives the residual representation
$`\bar\rho_{E,p} : G_K \to \mathrm{GL}_2(\mathbb{F}_p)`$ on $`E[p]`$.

### 2.2 Continuity

$`\rho_{E,p}`$ is continuous for the $`p`$-adic topology on $`T_pE`$, and the
reason is arithmetic: the action on $`E[p^n]`$ already factors through the
finite extension
$$K_n = K\bigl(E[p^n]\bigr),$$
the field generated by the coordinates of the $`p^n`$-torsion points, because a
Galois automorphism that fixes those coordinates fixes every point of
$`E[p^n]`$. An element $`\sigma`$ of $`G_K`$ therefore acts on $`E[p^n]`$ through
a finite quotient, and it moves points of $`T_pE`$ by an element of
$`p^n T_pE`$ once it fixes $`K_n`$. Passing to the limit gives the formal
statement the FLT development calls *adic continuity*: for every $`n`$ there is a
finite extension $`L/K`$ such that $`\sigma`$ fixing $`L`$ sends every $`x`$ to
$`x + (\text{something in } p^n T_pE)`$ — i.e. $`\rho_{E,p}(\sigma) - 1`$ lies in
$`p^n \mathrm{End}(T_pE)`$ (with $`\rho`$ viewed as an endomorphism).

### 2.3 The determinant: the Weil pairing

The Weil pairing
$$e_{p^n} : E[p^n] \times E[p^n] \longrightarrow \mu_{p^n}$$
is alternating, non-degenerate, and Galois-equivariant:
$`e_{p^n}(\sigma P, \sigma Q) = \sigma(e_{p^n}(P,Q))`$ (see
[base/007](../base/007-weil-pairing.md)). Passing to the limit gives a perfect
$`\mathbb{Z}_p`$-bilinear pairing on $`T_pE`$. For a
$`\mathbb{Z}_p`$-basis $`(e_1,e_2)`$ the value $`e(e_1,e_2)`$ is a
$`\mathbb{Z}_p`$-basis of $`\varprojlim \mu_{p^n} \cong \mathbb{Z}_p(1)`$, and
equivariance says exactly that the determinant of the representation is the
cyclotomic character:
$$\det \rho_{E,p} \\;=\\; \chi_p,$$
where $`\chi_p : G_K \to \mathbb{Z}_p^\times`$ is $`\sigma \mapsto \varprojlim \sigma(\zeta_{p^n})/\zeta_{p^n}`$.
Indeed, for a basis $`(e_1,e_2)`$ one computes
$$e(\sigma e_1, \sigma e_2) = \det\rho_{E,p}(\sigma)\cdot e(e_1,e_2)
  \quad\text{and}\quad
  e(\sigma e_1, \sigma e_2) = \sigma\bigl(e(e_1,e_2)\bigr) = \chi_p(\sigma)\cdot e(e_1,e_2),$$
and $`e(e_1,e_2)`$ is a unit, so the two scalars agree. Modulo $`p`$ this is
$`\det\bar\rho_{E,p} = \bar\chi_p`$, the mod-$`p`$ cyclotomic character.

### 2.4 Frobenius and the point count

Let $`K`$ be a number field and $`\ell \ne p`$ a prime of good reduction for
$`E`$. The action of $`G_K`$ on $`T_pE`$ is unramified at $`\ell`$, and for an
arithmetic Frobenius $`\mathrm{Frob}_\ell`$ the characteristic polynomial of
$`\rho_{E,p}(\mathrm{Frob}_\ell)`$ is
$$X^2 - a_\ell(E)\\,X + \ell, \qquad a_\ell(E) \\;=\\; \ell + 1 - \\#E(\mathbb{F}_\ell),$$
the numerator of the local zeta function of $`E`$ at $`\ell`$. The constant term
$`\ell`$ is the value of $`\chi_p`$ at $`\mathrm{Frob}_\ell`$, matching §2.3. The
same polynomial, reduced modulo $`p`$, is the characteristic polynomial of
$`\bar\rho_{E,p}(\mathrm{Frob}_\ell)`$ acting on $`E[p]`$ — this is the arithmetic
content of the Tate module, and it is what the word *attached* means: the
representation is attached to $`E`$ when its Frobenius traces are the point
counts.

### 2.5 Stable lines and isogenies

A one-dimensional $`\mathbb{F}_p`$-subspace of $`E[p]`$ stable under $`G_K`$ is
the same thing as the kernel of a $`K`$-rational $`p`$-isogeny $`E \to E'`$:
the quotient $`E/\ker\phi`$ is again an elliptic curve over $`K`$ exactly when
the kernel is Galois-stable. So *reducibility of $`\bar\rho_{E,p}`$* and *the
existence of a rational $`p`$-isogeny* are the same statement — the equivalence
[note 004](004-irreducible-and-cofixed-line.md) turns into the "cofixed line"
form used in the proof. In the FLT development the stable subspace is
`IsGaloisStable` and irreducibility is `GaloisRepIsIrreducible`; on the Frey
curve the residual representation has no stable line for $`p \ge 17`$, which is
Mazur's irreducibility theorem in the form the argument needs.

## 3. What the proof reads off the attached representation

For the Frey curve $`E_P`$ attached to a putative solution, the proof studies
$`\bar\rho_{E_P,p}`$. The relevant properties, stated on the representation
rather than the curve, are:

* **irreducibility** — no Galois-stable line in $`E_P[p]`$ (Mazur's theorem, in
  the strength the argument needs);
* **oddness** — complex conjugation acts with determinant $`-1`$, the
  Hodge-theoretic signature of a representation coming from an elliptic curve;
* **absolute irreducibility** — irreducibility is preserved after extending
  scalars, which modularity lifting needs;
* **determinant** — the cyclotomic character, from §2.3;
* **unramified outside $`pN`$** — where $`N`$ is the conductor, from good
  reduction;
* **Frobenius polynomials** — $`X^2 - a_\ell X + \ell`$, from §2.4, which is what
  a modularity statement compares against Hecke eigenvalues.

The formal counterparts are the structure `ResidualGaloisRep` and its predicates
`IsIrreducible`, `IsOdd`, `IsAbsolutelyIrreducible`, `IsUnramifiedAt`, together
with `IsAttachedTo`, which says precisely that the Frobenius characteristic
polynomial agrees with the Hecke polynomial of a cusp form. The Frey curve
itself contributes only a one-line instance, `FreyPackage.freyGaloisRep`.

## 4. The modular side: $`J_0(N)`$ and Eichler–Shimura

The second source of Galois representations is the Jacobian of the modular
curve, and this is the construction that makes "modularity" a statement about
the same kind of object.

### 4.1 The Tate module of $`J_0(N)`$

Let $`X_0(N)`$ be the modular curve and
$$J_0(N) \\;=\\; \mathrm{Pic}^0(X_0(N))$$
its degree-zero divisor class group, an abelian variety of dimension $`g`$ over
$`\mathbb{Q}`$ ([math/009 §2.1](009-hecke-jacobian-commute.md) explains why the
degree-zero classes are the Jacobian; the FLT development builds it on the
function field of $`X_0(N)`$). Its $`p`$-power torsion is an
inverse system exactly as in §1, and
$$T_p J_0(N) \\;\cong\\; \mathbb{Z}_p^{\\,2g}, \qquad
  V_p J_0(N) \\;\cong\\; \mathbb{Q}_p^{\\,2g}.$$
Since $`J_0(N)`$ is defined over $`\mathbb{Q}`$, the absolute Galois group acts,
giving
$$\rho_{J_0(N),p} : G_{\mathbb{Q}} \to \mathrm{GL}_{2g}(\mathbb{Z}_p).$$

### 4.2 The Hecke action and the eigenform decomposition

The Hecke operators $`T_\ell`$ (and the diamond operators) act on $`J_0(N)`$ by
correspondences and commute with the Galois action, because the correspondences
are defined over $`\mathbb{Q}`$; that is the mathematical content of
[math/009](009-hecke-jacobian-commute.md). Let
$$\mathbb{T} \\;=\\; \mathbb{Z}\bigl[T_\ell : \ell \text{ prime}\bigr]
\\;\subseteq\\; \mathrm{End}(J_0(N))$$
be the Hecke algebra. Then $`T_pJ_0(N)`$ is a module over $`\mathbb{T}`$, and the
two actions — Hecke and Galois — commute.

Now let $`f \in S_2(\Gamma_0(N))`$ be a normalised eigenform with
$`T_\ell f = a_\ell f`$. The system of eigenvalues defines a ring homomorphism
$$\varphi_f : \mathbb{T} \to \bar{\mathbb{Q}}_p, \qquad T_\ell \mapsto a_\ell,$$
and the $`f`$-isotypic piece of $`V_pJ_0(N) \otimes_{\mathbb{Q}_p} \bar{\mathbb{Q}}_p`$
is a two-dimensional representation of $`G_{\mathbb{Q}}`$ over
$`\bar{\mathbb{Q}}_p`$. This is the
Galois representation attached to $`f`$:
$$\rho_f : G_{\mathbb{Q}} \to \mathrm{GL}_2(\bar{\mathbb{Q}}_p),$$
unramified outside $`pN`$, with
$$\mathrm{tr}\\,\rho_f(\mathrm{Frob}_\ell) = a_\ell, \qquad
  \det\rho_f(\mathrm{Frob}_\ell) = \ell \quad (\ell \nmid pN),$$
the determinant again by §2.3 (weight two, trivial nebentypus). Reducing a
suitable $`\mathbb{Z}_p`$-lattice modulo the maximal ideal gives the residual
representation $`\bar\rho_f`$ with characteristic polynomial
$`X^2 - a_\ell X + \ell \bmod \mathfrak{p}`$.

*Modularity of $`E`$* is the statement that some $`\rho_f`$ has the same
Frobenius traces as $`\rho_{E,p}`$ — equivalently, that the two representations
are isomorphic after semisimplification. That is exactly the shape in which FLT
states it, and why the proof can move between curves and forms at the level of
representations.

### 4.3 Eichler–Shimura

The bridge between the analytic and cohomological pictures is the Eichler–Shimura
isomorphism. For the compact Riemann surface $`X_0(N)(\mathbb{C})`$,
$$H^1\bigl(X_0(N)(\mathbb{C}), \mathbb{Q}\bigr) \\;\cong\\;
  S_2(\Gamma_0(N)) \oplus \overline{S_2(\Gamma_0(N))},$$
the two summands being the holomorphic and anti-holomorphic halves of the Hodge
decomposition of $`H^1`$ of the Jacobian. The Hecke operators act on both sides,
and the isomorphism is equivariant for them; it is realised analytically by
integrating the cusp form along paths (the period map, or Eichler–Shimura map).
Concretely, $`S_2(\Gamma_0(N))`$ is the cotangent space at the origin of
$`J_0(N)`$ and the holomorphic differentials on $`X_0(N)`$ are the cusp forms of
weight two, so the isomorphism is the statement
$`H^1(J_0(N),\mathbb{Q}) \cong H^1(X_0(N),\mathbb{Q})`$ combined with the Hodge
decomposition. The upshot for the Galois side: the two-dimensional pieces of
$`V_pJ_0(N)`$ indexed by eigenforms are exactly the representations
$`\rho_f`$ of §4.2, and the Hecke eigenvalues are their Frobenius traces.

## 5. How the formalization writes it

The FLT development builds the Tate module explicitly as a projective limit
inside a product, rather than invoking a general categorical limit. This is worth
seeing once, because it makes the rank computation and the Galois action
concrete.

### 5.1 The limit, and rank two

`TateModule p M` for an abelian group $`M`$ with a monoid action is the
`AddSubgroup` of $`\prod_{n \in \mathbb{N}} M`$ cut out by the two conditions
$$p^n \cdot x_n = 0, \qquad p \cdot x_{n+1} = x_n$$
([Def_EllipticCurve_TateModule.lean, lines 15–23](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_TateModule.lean#L15-L23)).
Under the cardinality hypothesis
$$hcard : \forall n,\ \\#M[p^n] = (p^n)^2$$
the file proves the $`\mathbb{Z}_p`$-module is free of rank two: `basisOfCard`
produces a $`\mathbb{Z}_p`$-basis, `linearIndependent_pair` the independence,
`free` the freeness, and `finrank_eq_two` the rank
([lines 596, 622, 630](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_TateModule.lean#L596-L640)).
The mathematics is §1.2; the work is linear algebra over $`\mathbb{Z}_p`$ and
`ZMod`.

### 5.2 The Galois action, concretely

`TateModule.rep` turns a monoid action on $`M`$ into a ring homomorphism
$`G \to \mathrm{End}_{\mathbb{Z}_p}(T_pM)`$ by acting coordinatewise,
$`(g \cdot x)_n = g \cdot x_n`$
([lines 174–190](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_TateModule.lean#L174-L193));
this is §2.1. For $`W`$ over $`\mathbb{Q}`$ the file defines the torsion field
$`\mathbb{Q}(E[p^n])`$ (`torsionField`, [line 689](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_TateModule.lean#L689-L693)),
proves it finite over $`\mathbb{Q}`$, and derives adic continuity
(`tateModule_isAdicContinuous`, [lines 725–731](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_TateModule.lean#L725-L731)),
which is §2.2. Packaging the basis gives `tateModuleRep`, a
`GaloisRepAdic ℤ_[p]`
([lines 851–855](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_TateModule.lean#L851-L855)).

The target structure `GaloisRepAdic` records: a free finite module $`V`$ over a
local ring $`A`$ with $`\mathrm{finrank}_A V = 2`$, a monoid homomorphism
$`\rho`$, and `GaloisActionIsAdicContinuous` — for every $`n`$ a finite level
$`L`$ such that fixing $`L`$ makes $`\rho(\sigma) - 1`$ divisible by
$`\mathfrak{m}_A^n`$
([Def_GaloisRep_Adic.lean, lines 9–28](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Adic.lean#L9-L28)).
At $`A = \mathbb{Z}_p`$ this is $`\rho_{E,p}`$; the residual version
`ResidualGaloisRep` is the same structure over a field $`k`$, with
$`V = E[p]`$, $`\dim_k V = 2`$ forced by $`hcard`$ through
`Module.natCard_eq_pow_finrank`, and the predicates of §3 defined on it
([Def_GaloisRep_Residual.lean, lines 22–63 and 87–103](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean#L22-L103)).

### 5.3 The modular side

Here the abelian group is $`J = J_0(N)`$, carrying a `HeckeAlg`-module structure
with $`\mathbb{T} = \mathbb{Z}[T_\ell : \ell\ \text{prime}]`$ realised as
`MvPolynomial Nat.Primes ℤ`
([Def_HeckeGalois_EichlerShimura.lean, lines 14–26](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean#L14-L26)).
`ModularCurve.TateModule p J` is the submodule of $`\prod_n J`$ of §5.1, taken
inside the Hecke-module category
([Def_ModularCurve_EichlerShimuraData.lean, lines 15–26](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_EichlerShimuraData.lean#L15-L26));
`tateHeckeRep` is the Hecke action and `rationalGaloisRep` the Galois action
after tensoring with $`\mathbb{Q}_p`$
([Def_ModularCurve_JZeroTateModule.lean, lines 20–77](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_JZeroTateModule.lean#L20-L77)).

The automorphic hypotheses are bundled as data. `EichlerShimuraData` is the
structure holding four properties
([lines 100–108](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_EichlerShimuraData.lean#L100-L108)):

* `FreeOfRankTwo` — the rank-two statement of §4.1 in the form the proof needs:
  two elements generate $`T_pJ`$ up to $`p`$-power torsion, and no nonzero Hecke
  relation holds between them;
* `UnramifiedOutside` — $`\sigma`$ in the inertia group at $`\ell \nmid Np`$ acts
  trivially on $`p`$-power torsion;
* `FrobeniusQuadratic` — the Cayley–Hamilton relation
  $`\sigma^2 x - T_\ell(\sigma x) + \ell x = 0`$, i.e. the characteristic
  polynomial $`X^2 - T_\ell X + \ell`$ of §4.2, with the Hecke operator as the
  trace;
* `EigenformSupport` — a $`p`$-torsion module is nonzero at every maximal ideal
  cut out by a normalised eigenform, which ties the abstract Hecke module to
  actual forms.

`IsLambdaAdicRealization` then records the realisation of this data on a
two-dimensional $`k`$-vector space: an additive $`\pi`$ commuting with both the
Galois action ($`\pi(\sigma x) = \rho(\sigma)\pi x`$) and the Hecke action
($`\pi(t x) = \varphi(t)\pi x`$) and spanning
([lines 176–190](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_EichlerShimuraData.lean#L176-L190)).
Finally `CuspForm.HeckeGaloisRepDatum` bundles, for the patching argument, a
deformation-ring presentation $`\pi : \mathbb{T} \to T`$ together with a
`GaloisRepAdic` whose Frobenius characteristic polynomials are
$`X^2 - \pi(T_\ell) X + \ell`$ and whose residual representation is absolutely
irreducible
([Def_CuspForm_HeckeGaloisRepDatum.lean, lines 8–38](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeGaloisRepDatum.lean#L8-L38)).
The residual attachment predicate `IsAttachedTo` is the same comparison in the
curve direction: the Frobenius characteristic polynomial equals the Hecke
polynomial of a cusp form
([Def_GaloisRep_Residual.lean, lines 48–55](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean#L48-L55)).

### 5.4 The one arithmetic input

Every rank-two statement above is conditional on $`hcard`$, the cardinality
$`\#E[p^n] = (p^n)^2`$. That is the single arithmetic input; it is the theorem of
[note 005](005-card-torsion-p-squared.md), `card_torsion_of_isAlgClosed`, and it
is already ported in this project as `FLTForHuman/Elliptic/TorsionCard.lean`.
Everything else in the elliptic-curve construction is $`\mathbb{Z}_p`$-linear
algebra and the group action.

## 6. Key points, and where they are formalized

| mathematical point | Lean declaration | file |
|---|---|---|
| the limit $`T_pM \subset \prod_n M`$ | `TateModule` | `Def_EllipticCurve_TateModule.lean:15` |
| rank two from $`\#M[p^n] = (p^n)^2`$ | `basisOfCard`, `free`, `finrank_eq_two` | `:596`, `:622`, `:630` |
| coordinatewise Galois action | `TateModule.rep` | `:174` |
| $`\mathbb{Q}(E[p^n])`$ is finite | `torsionField`, `finiteDimensional_torsionField` | `:689`, `:703` |
| adic continuity | `tateModule_isAdicContinuous` | `:725` |
| $`\rho_{E,p}`$ on a basis | `tateModuleRepOfBasis`, `tateModuleRep` | `:740`, `:851` |
| the ambient structure, rank 2 and continuity | `GaloisRepAdic`, `GaloisActionIsAdicContinuous` | `Def_GaloisRep_Adic.lean:16`, `:9` |
| residual representation and its predicates | `ResidualGaloisRep`, `IsIrreducible`, `IsOdd`, `IsAbsolutelyIrreducible`, `IsUnramifiedAt` | `Def_GaloisRep_Residual.lean:22`, `:61`, `:57`, `:82`, `:44` |
| Frobenius trace equals Hecke eigenvalue | `IsAttachedTo` | `Def_GaloisRep_Residual.lean:48` |
| Frey-curve instance | `FreyPackage.freyGaloisRep` | `Def_FreyPackage_GaloisRep.lean:38` |
| Hecke algebra $`\mathbb{T}`$ | `HeckeAlg` | `Def_HeckeGalois_EichlerShimura.lean:14` |
| $`T_pJ`$ as a Hecke submodule | `ModularCurve.TateModule` | `Def_ModularCurve_EichlerShimuraData.lean:15` |
| Hecke and Galois actions on $`T_pJ`$ | `tateHeckeRep`, `rationalGaloisRep` | `Def_ModularCurve_JZeroTateModule.lean:20`, `:48` |
| rank two, unramified, Frobenius, eigenform support | `EichlerShimuraData` | `Def_ModularCurve_EichlerShimuraData.lean:100` |
| realisation on a 2-dimensional space | `IsLambdaAdicRealization` | `Def_ModularCurve_EichlerShimuraData.lean:176` |
| the $`R = T`$ datum | `HeckeGaloisRepDatum` | `Def_CuspForm_HeckeGaloisRepDatum.lean:8` |

## 7. What this note does not cover

The Tate module is where the arithmetic *starts*, not where it ends. Three
neighbouring subjects are deliberately out of scope here:

* **Galois cohomology and deformations** — the tangent space
  $`H^1(G_{\mathbb{Q}}, \mathrm{ad}\,\bar\rho)`$, deformation rings, and the
  $`R = T`$ isomorphism that consumes `HeckeGaloisRepDatum`. These are the
  arithmetic core of the modularity-lifting step.
* **$`p`$-adic Hodge theory** — flat, crystalline and ordinary conditions on
  $`\rho_{E,p}`$ at $`p`$, which the proof needs in the level-conditioned lifting
  theorems.
* **The local Langlands correspondence and automorphic representations** — the
  analytic input to Langlands–Tunnell, where the representation-theoretic side is
  developed adelically rather than through $`J_0(N)`$.

## Links

- FLT at the pinned sha `aa2d8b3`:
  [`Def_EllipticCurve_TateModule.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_TateModule.lean),
  [`Def_GaloisRep_Adic.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Adic.lean),
  [`Def_GaloisRep_Residual.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean),
  [`Def_ModularCurve_JZeroTateModule.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_JZeroTateModule.lean),
  [`Def_ModularCurve_EichlerShimuraData.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_EichlerShimuraData.lean),
  [`Def_HeckeGalois_EichlerShimura.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean),
  [`Def_CuspForm_HeckeGaloisRepDatum.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeGaloisRepDatum.lean),
  [`Def_FLTPrelim_GaloisRep.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean),
  [`Def_FreyPackage_GaloisRep.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FreyPackage_GaloisRep.lean).
- Generated module glosses: the author's static copy,
  <https://tianyipeng.github.io/fermats-last-theorem/def/EllipticCurve_TateModule.html>
  and the sibling pages linked from it.
- Companion notes in this project: [005](005-card-torsion-p-squared.md),
  [003](003-galois-rep-irreducible-in-english.md),
  [004](004-irreducible-and-cofixed-line.md),
  [009](009-hecke-jacobian-commute.md), and the foundations
  [base/007](../base/007-weil-pairing.md), [base/014](../base/014-hecke-operators.md).
- The port that supplies the arithmetic input:
  `FLTForHuman/Elliptic/TorsionCard.lean` in `lean/`.
