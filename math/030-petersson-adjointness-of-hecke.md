# The Petersson adjointness of the Hecke operator on a nebentypus component

**Status.** Mathematical exposition, pinned to the FLT commit `aa2d8b3`; the port
is cross-referenced at commit `2d8e5c1` of
[`htzh/flt_for_human`](https://github.com/htzh/flt_for_human). This note explains the classical
adjointness

$$\langle T_p f, g\rangle \\;=\\; \overline{\varepsilon(p)} \\, \langle f, T_p g\rangle$$

for cusp forms of weight $`k`$, level $`\Gamma_1(N)`$ and nebentypus
$`\varepsilon`$, the unfolding/double-coset proof behind it, and the two
consequences the Deligne–Serre column uses: the conjugation relation for Hecke
eigenvalues and the existence of a basis of nebentypus Hecke eigenforms. The Lean
statements are collected in §7.

Companions: [019-deligne-serre-weight-one.md](019-deligne-serre-weight-one.md)
(the weight-one theorem where both consequences are consumed),
[009-hecke-jacobian-commute.md](009-hecke-jacobian-commute.md) ($`T_p`$ and the
diamond operators commute — the other half of the Hecke algebra),
[015-weight-two-hecke-periods.md](015-weight-two-hecke-periods.md) (weight-two
Petersson products and periods), and the port records
[../lean/topics/deligneSerre/TOPIC-petersson-hecke-adjointness.md](../lean/topics/deligneSerre/TOPIC-petersson-hecke-adjointness.md)
and [../lean/topics/PORTING-DeligneSerre.md](../lean/topics/PORTING-DeligneSerre.md).

## 1. Cusp forms with a nebentypus

Let $`N \ge 1`$ and $`k \in \mathbb{Z}`$. Write $`\mathbb{H} = \{\tau \in \mathbb{C} : \mathrm{Im}\,\tau > 0\}`$
for the upper half-plane, $`\mathrm{SL}_2(\mathbb{Z})`$ for the modular group, and

$$\Gamma_0(N) = \Bigl\\{\begin{pmatrix} a & b \\\\ c & d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z}) : N \mid c\Bigr\\},
\qquad
\Gamma_1(N) = \Bigl\\{\begin{pmatrix} a & b \\\\ c & d\end{pmatrix} \in \Gamma_0(N) : a \equiv d \equiv 1 \pmod N\Bigr\\},$$

so that $`\Gamma_1(N) \subseteq \Gamma_0(N)`$ is the kernel of the reduction
$`\Gamma_0(N) \to (\mathbb{Z}/N\mathbb{Z})^\times`$, $`\gamma \mapsto \gamma_{11}`$.

**The weight-$`k`$ slash.** For $`\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \mathrm{GL}_2(\mathbb{Q})`$
with $`\det \gamma > 0`$ and a function $`f : \mathbb{H} \to \mathbb{C}`$, put

$$(f \mid_k \gamma)(\tau) \\;=\\; \det(\gamma)^{k-1}\\,(c\tau+d)^{-k}\\, f(\gamma\tau),
\qquad
\gamma\tau = \frac{a\tau+b}{c\tau+d}.$$

The factor $`\det(\gamma)^{k-1}`$ is what makes the slash an action on all of
$`\mathrm{GL}_2(\mathbb{Q})^+`$, not only on the unimodular group:
$`(f \mid_k \gamma \delta) = ((f \mid_k \gamma) \mid_k \delta)`$. On
$`\mathrm{SL}_2(\mathbb{Z})`$ it reduces to the familiar
$`(f \mid_k \gamma)(\tau) = (c\tau+d)^{-k} f(\gamma\tau)`$. It matters below
because the Hecke matrices have determinant $`p`$, and the normalization is the
one that makes the operator self-adjoint for trivial nebentypus.

**Nebentypus.** Let $`\varepsilon : (\mathbb{Z}/N\mathbb{Z})^\times \to \mathbb{C}^\times`$
be a Dirichlet character, extended to $`\mathbb{Z}/N\mathbb{Z}`$ by
$`\varepsilon(a) = 0`$ when $`a`$ is not a unit. A cusp form $`f \in S_k(\Gamma_1(N))`$
has **nebentypus** $`\varepsilon`$ when

$$f \mid_k \gamma \\;=\\; \varepsilon(\gamma_{11})\\, f
\qquad \text{for every } \gamma \in \Gamma_0(N).$$

The notation is legitimate because $`\gamma_{11}`$ is a unit modulo $`N`$ for
$`\gamma \in \Gamma_0(N)`$: the determinant condition gives
$`\gamma_{00}\gamma_{11} \equiv 1 \pmod N`$. Equivalently, $`f`$ is an
eigenvector with eigenvalue $`\varepsilon(d)`$ for every diamond operator
$`\langle d\rangle`$; the subspace of such forms is written
$`S_k(\Gamma_1(N), \varepsilon)`$. The theorem below is stated inside the
$`\varepsilon`$-component; the conjugate character enters only through the scalar
$`\overline{\varepsilon(p)}`$ in the adjointness relation.

## 2. The Petersson product

For $`f, g : \mathbb{H} \to \mathbb{C}`$ and $`\tau = x+iy`$, the **Petersson
density** is

$$D_{f,g}(\tau) \\;=\\; \overline{f(\tau)}\\, g(\tau)\\, y^k,
\qquad d\mu = y^{-2}\\,dx\\,dy .$$

It is invariant under the slash action of $`\mathrm{SL}_2(\mathbb{Z})`$: for
$`\gamma \in \mathrm{SL}_2(\mathbb{Z})`$, the two factors of
$`(c\tau+d)^{-k}`$ and the change $`\mathrm{Im}(\gamma\tau) = \mathrm{Im}\,\tau/|c\tau+d|^2`$
cancel, so

$$D_{f \mid_k \gamma,\\; g \mid_k \gamma}(\tau) \\;=\\; D_{f,g}(\tau).$$

Since $`\Gamma_1(N) \subseteq \mathrm{SL}_2(\mathbb{Z})`$, the density is also
$`\Gamma_1(N)`$-invariant, and the **Petersson product** is

$$\langle f, g\rangle_{\Gamma_1(N)} \\;=\\; \int_{\Gamma_1(N) \backslash \mathbb{H}} \overline{f(\tau)}\\,g(\tau)\\,y^k \\, d\mu .$$

The integral converges for cusp forms: $`|f|^2 y^k`$ is bounded on the standard
fundamental domain and decays at the cusps. It is positive definite,
$`\langle f,f\rangle > 0`$ for $`f \ne 0`$, because $`|f|^2 y^k`$ is continuous and
nonnegative, and strictly positive on a set of positive measure. Note the
convention: **antilinear in the first slot, linear in the second**, which is the
number-theory convention and the one FLT and its port use. Some textbooks
conjugate the second slot instead; every formula below is adjusted to this
convention.

**Unfolding.** For a finite-index subgroup $`\Gamma \subseteq \mathrm{SL}_2(\mathbb{Z})`$
and the standard fundamental domain $`\mathcal{D}`$ of
$`\mathrm{SL}_2(\mathbb{Z})`$, the quotient
$`\Gamma \backslash \mathbb{H}`$ is tiled by the translates
$`q^{-1}\mathcal{D}`$, $`q \in \mathrm{SL}_2(\mathbb{Z})/\Gamma`$, and the
$`\Gamma`$-invariance of the density gives the identity

$$\langle f, g\rangle_{\Gamma}
\\;=\\; \int_{\mathcal{D}} \sum_{q \in \mathrm{SL}_2(\mathbb{Z})/\Gamma}
D_{f,g}(q^{-1}\tau)\\, d\mu(\tau).$$

This is exactly how the FLT development defines the product in practice: the
port's `peterssonOn` is the integral over $`\mathcal{D}`$ of the coset sum of
the pointwise density $`\overline{f} g`$, indexed by
$`\mathrm{SL}_2(\mathbb{Z}) \sslash \Gamma_1(N)`$. The coset sum is what
replaces the quotient $`\Gamma_1(N)\backslash\mathbb{H}`$; its convergence is
the convergence of the integral, and the two are the same number.

Finally, $`S_k(\Gamma_1(N))`$ is finite-dimensional over $`\mathbb{C}`$; this is
what makes the spectral arguments of §6 work.

## 3. The Hecke operator $`T_p`$

Fix a prime $`p`$ with $`p \nmid N`$ ($`p`$ is *good* for the level). Define two
operators on functions $`\mathbb{H} \to \mathbb{C}`$:

$$U_p f \\;=\\; \sum_{j=0}^{p-1} f \mid_k \begin{pmatrix}1 & j \\\\ 0 & p\end{pmatrix},
\qquad
V_p f \\;=\\; f \mid_k \begin{pmatrix}p & 0 \\\\ 0 & 1\end{pmatrix}.$$

With the determinant convention of §1 the two terms have very different shapes:

$$\bigl(f \mid_k \begin{pmatrix}1 & j \\\\ 0 & p\end{pmatrix}\bigr)(\tau)
= p^{-1}\\, f\bigl(\tfrac{\tau+j}{p}\bigr),
\qquad
\bigl(f \mid_k \begin{pmatrix}p & 0 \\\\ 0 & 1\end{pmatrix}\bigr)(\tau)
= p^{k-1}\\, f(p\tau).$$

The first is an average over the $`p`$ residue classes (each term carries the
$`p^{-1}`$ from $`\det^{k-1}(c\tau+d)^{-k}`$, and the averaging over the $`j`$
cancels it); the second is the $`p`$-dilation with the $`p^{k-1}`$ that makes the
normalized Hecke operator.

**The operator on the $`\varepsilon`$-component.** On
$`S_k(\Gamma_1(N), \varepsilon)`$ one takes

$$T_p f \\;=\\; U_p f \\;+\\; \varepsilon(p)\\, V_p f .$$

The scalar $`\varepsilon(p)`$ is not cosmetic: it is the eigenvalue of the
diamond operator $`\langle p\rangle`$ on the component, and it is exactly what
makes $`T_p`$ preserve $`S_k(\Gamma_1(N), \varepsilon)`$: without the factor the
dilation term does not obey the nebentypus law of the component. The two terms
correspond to the two parts of the double coset

$$\Gamma_1(N) \begin{pmatrix}p & 0 \\\\ 0 & 1\end{pmatrix} \Gamma_1(N)
\\;=\\; \bigsqcup_{j=0}^{p-1} \Gamma_1(N)\begin{pmatrix}1 & j \\\\ 0 & p\end{pmatrix}
\\;\sqcup\\; \Gamma_1(N)\begin{pmatrix}p & 0 \\\\ 0 & 1\end{pmatrix},$$

a disjoint union of $`p+1`$ left cosets. The hypothesis $`p \nmid N`$ is what
makes this decomposition behave well for $`\Gamma_1(N)`$ (the level is
$`p`$-suitable): every $`\gamma \in \Gamma_1(N)`$ has a unique representative
$`\gamma = r_i \lambda`$ with $`\lambda`$ in the intersection

$$\Lambda \\;=\\; \Gamma_1(N) \cap \Gamma^0(p),
\qquad \Gamma^0(p) = \Bigl\\{\begin{pmatrix}a&b\\\\c&d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z}) : p \mid b\Bigr\\},$$

and $`r_i`$ running over the $`p+1`$ representatives above. Thus
$`[\Gamma_1(N) : \Lambda] = p+1`$ — the index that becomes the $`p+1`$ terms of
$`T_p`$.

**$`q`$-expansion.** Write $`q = e^{2\pi i\tau}`$ and
$`f = \sum_{n \ge 1} a_n q^n`$. Summing the $`p`$ terms of $`U_p`$,

$$U_p f \\;=\\; p^{-1} \sum_{j=0}^{p-1} \sum_{n \ge 1} a_n q^{n/p}\\, \zeta_p^{nj}
\\;=\\; \sum_{m \ge 1} a_{pm}\\, q^m,
\qquad \zeta_p = e^{2\pi i/p},$$

because $`\sum_j \zeta_p^{nj}`$ is $`p`$ when $`p \mid n`$ and $`0`$ otherwise.
And $`V_p f = p^{k-1} \sum_n a_n q^{pn}`$. Hence

$$a_n(T_p f) \\;=\\; a_{pn}(f) \\;+\\; \varepsilon(p)\\, p^{k-1}\\, a_{n/p}(f),
\qquad a_{n/p}(f) = 0 \text{ if } p \nmid n.$$

This is the coefficient form in which the two consumers of §6 state their
hypotheses: an eigenform with eigenvalue $`\lambda`$ satisfies
$`a_n(T_p f) = \lambda\, a_n(f)`$ for all $`n`$.

## 4. The theorem

> **Theorem (Petersson adjointness; Diamond–Shurman 5.5.3, Miyake 4.5.4,
> Shimura Prop. 3.39).** Let $`N \ge 1`$, $`k \in \mathbb{Z}`$, let
> $`\varepsilon`$ be a Dirichlet character modulo $`N`$, let $`p`$ be a prime
> with $`p \nmid N`$, and let $`f, g \in S_k(\Gamma_1(N), \varepsilon)`$.
> Then
> $$\langle T_p f, g\rangle \\;=\\; \overline{\varepsilon(p)} \\, \langle f, T_p g\rangle.$$

Since $`|\varepsilon(p)| = 1`$ for a unit $`p`$, the scalar is a root of unity
and equals $`\varepsilon(p)^{-1}`$. In the language of adjoints with the
convention of §2 (antilinear in the first slot), the theorem says
$`T_p^* = \overline{\varepsilon(p)}\,T_p`$: $`T_p`$ is self-adjoint on the
trivial-nebentypus component, and on a general component it is self-adjoint up
to the diamond character. That is the whole content: the Hecke algebra acts by
normal operators for the Petersson product.

**Normalization warning.** With the *unnormalized* dilation
$`\tilde V_p f(\tau) = f(p\tau)`$ and the unnormalized average
$`\tilde U_p f = \sum_j f((\tau+j)/p)`$, the same proof gives the factor
$`\overline{\varepsilon(p)}\,p^{k-1}`$ (or $`p^{1-k}`$, depending on the
choice). The determinant convention of §1, $`V_p = p^{k-1}f(p\tau)`$, is the one
used in the theorem above and in FLT; it is the normalization under which the
operator is genuinely (almost) self-adjoint.

## 5. The proof

The proof has three ingredients: an adjunction formula for a single slash, the
unfolding of the Petersson integral over the $`p+1`$ cosets, and the nebentypus
identity that produces the character factor. The first is elementary
calculus on $`\mathbb{H}`$; the second and third are the substance.

### 5.1 Adjunction for a slash

> **Lemma.** Let $`\alpha \in \mathrm{GL}_2(\mathbb{Q})`$ with
> $`\det(\alpha) > 0`$, and put $`\alpha^* = \det(\alpha)\,\alpha^{-1}`$
> (the adjugate). For cusp forms $`f, g`$ for which both integrals converge,
> $$\langle f \mid_k \alpha,\\; g\rangle \\;=\\; \langle f,\\; g \mid_k \alpha^*\rangle.$$

*Sketch.* Write $`j(\alpha,\tau) = c\tau+d`$ for the denominator. Substituting
$`\tau = \alpha^{-1}w`$ in the left integral and using
$`d\mu(\alpha^{-1}w) = d\mu(w)`$ together with
$`\mathrm{Im}(\alpha^{-1}w) = \det(\alpha)^{-1}|j(\alpha^{-1},w)|^2\,\mathrm{Im}\,w`$,
the two determinant factors cancel and the cocycle relation
$`j(\alpha, \alpha^{-1}w)\,j(\alpha^{-1},w) = 1`$ leaves
$`\overline{f(w)}\,(g \mid_k \alpha^*)(w)\,\mathrm{Im}(w)^k`$. $`\square`$

For the diagonal matrix $`\alpha = \mathrm{diag}(p,1)`$ the lemma reads
$`\langle V_p f, g\rangle = \langle f, g \mid_k \mathrm{diag}(1,p)\rangle`$:
the adjoint of the $`p`$-dilation is the $`p`$-contraction, as it must be. For
the unipotent representatives $`\alpha_j = \begin{pmatrix}1&j\\0&p\end{pmatrix}`$,
the adjugate is $`\alpha_j^* = \begin{pmatrix}p&-j\\0&1\end{pmatrix}
= \begin{pmatrix}1&-j\\0&1\end{pmatrix}\begin{pmatrix}p&0\\0&1\end{pmatrix}`$,
a unipotent translate of the $`p`$-dilation. Summed over $`j`$ and unfolded
against the coset sum, the $`p+1`$ adjugates reassemble into the same
$`\Lambda`$-coset sum: this is the classical pairing $`U_p \leftrightarrow V_p`$.

### 5.2 Unfolding over the $`p+1`$ cosets

The product is an integral over $`\Gamma_1(N)\backslash\mathbb{H}`$. The Hecke
operator is a sum over the $`p+1`$ left cosets in the double-coset identity of
§3, and the adjunction lemma converts each term into a slash on the *other*
form. Because the cosets meet in the common subgroup
$`\Lambda = \Gamma_1(N) \cap \Gamma^0(p)`$, the $`p+1`$ translates
$`\alpha_j^{-1}\mathcal{D}`$ tile a fundamental domain for $`\Lambda`$, and the two sides
$`\langle T_p f, g\rangle`$ and $`\langle f, T_p g\rangle`$ become integrals of
the *same* $`\Lambda`$-coset sum, over the same domain $`\mathcal{D}`$. In the
port, this reindexing is the identity `unfold_sum`: the coset sum over
$`\mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)`$ is rewritten as a sum over
$`\mathrm{SL}_2(\mathbb{Z})/\Lambda`$ together with the $`p+1`$ representatives
`rr hpN i`, $`i \in \mathrm{Option}(\mathrm{Fin}\,p)`$.

After unfolding, the two integrands are

$$\Phi(\tau) \\;=\\; \overline{(f \mid_k \alpha_0)(\tau)}\\, g(\tau)\\, y^k,
\qquad
\Psi(\tau) \\;=\\; \overline{f(\tau)}\\, (g \mid_k \alpha_0)(\tau)\\, y^k,
\qquad \alpha_0 = \begin{pmatrix}1&0\\\\0&p\end{pmatrix},$$

where $`\alpha_0`$ is the $`j=0`$ term: the $`U_p`$ sum and the $`V_p`$ term have
both been brought to a single $`\alpha_0`$-slash by the adjunction lemma. The
two integrals over $`\mathcal{D}`$ of the $`\Lambda`$-coset sums of $`\Phi`$ and
$`\Psi`$ are equal once one uses that the change of variables
$`\tau \mapsto \beta\tau`$, $`\beta = \gamma_\infty \alpha_0`$ with
$`\gamma_\infty \in \Gamma_0(N)`$, is measure-preserving and carries
$`\Lambda`$ to a subgroup $`\Lambda'`$ for which the coset sum is the same
(`integral_cosum_pair` in the port). This is the analytic heart: the
Petersson integral of a coset sum over $`\Lambda`$ depends only on
$`\Lambda`$-invariance, not on the choice of representatives, and $`\beta`$
changes the representatives without changing the integral.

### 5.3 The character factor

What is left is the comparison of the two integrands, and here the nebentypus
enters. Let $`\gamma_\infty \in \Gamma_0(N)`$ be a matrix whose lower-right
entry is congruent to $`p`$ modulo $`N`$ (in the port, the Bezout matrix
`gInf`, constructed from a solution of $`ap - bN = 1`$). For a form of
nebentypus $`\varepsilon`$,

$$f \mid_k \gamma_\infty \\;=\\; \varepsilon(\gamma_{\infty,11})\\, f
\\;=\\; \varepsilon(p)\\, f,$$

by the nebentypus law. Chasing the slash through the product
$`\gamma_\infty \alpha_0`$ gives the key identity

$$f \mid_k \mathrm{diag}(p,1) \\;=\\; \varepsilon(p)^{-1}\\, \bigl((f \mid_k \alpha_0) \mid_k \gamma_\infty\bigr),$$

which says that the $`V_p`$ term is the $`\alpha_0`$ term twisted by an element
of $`\Gamma_0(N)`$ whose nebentypus value is $`\varepsilon(p)`$. When this
twist is absorbed into the Petersson product, $`\gamma_\infty`$ acts on the
second slot and contributes $`\varepsilon(p)`$ (one $`\varepsilon(p)^{-1}`$
from the scalar in front, one $`\varepsilon(p)`$ from the nebentypus of the
second form), and the conjugation convention of §2 turns it into
$`\overline{\varepsilon(p)}`$. In the port this is the identity `Ψ_eq`:

$$\Psi(\tau) \\;=\\; \varepsilon(p)\\, \Phi\bigl((\gamma_\infty \alpha_0)\tau\bigr).$$

### 5.4 Assembly

The three steps combine without splitting $`T_p`$ into its $`U_p`$ and $`V_p`$
pieces separately: after §5.2, *both* sides of the adjointness are integrals
over $`\mathcal{D}`$ of a $`\Lambda`$-coset sum, one of $`\Phi`$ and one of
$`\Psi`$; §5.3 computes $`\Psi`$ from $`\Phi`$ by the twist
$`\beta = \gamma_\infty\alpha_0`$ and the scalar $`\varepsilon(p)`$; and §5.2
says the integral is invariant under that twist. Hence the two integrals differ
exactly by $`\varepsilon(p)`$, and with the conjugation convention of §2 the
adjointness reads

$$\langle T_p f, g\rangle \\;=\\; \overline{\varepsilon(p)}\\,\langle f, T_p g\rangle.$$

This is precisely the port's `main`: both sides are computed as integrals of
$`\Lambda`$-coset sums, the integrals are identified by `integral_cosum_pair`,
and the surviving scalar is $`\overline{\varepsilon(p)}`$.

## 6. Consequences

### 6.1 Conjugation of Hecke eigenvalues

Let $`f \in S_k(\Gamma_1(N), \varepsilon)`$ be a nonzero eigenform for $`T_p`$
with eigenvalue $`\lambda`$ (equivalently, $`a_p(f) = \lambda`$ when $`f`$ is
normalized with $`a_1 = 1`$). Applying the theorem with $`g = f`$:

$$\langle T_p f, f\rangle \\;=\\; \overline{\lambda}\\,\langle f, f\rangle,
\qquad
\langle f, T_p f\rangle \\;=\\; \lambda\\,\langle f, f\rangle,$$

and the theorem gives $`\overline{\lambda} = \overline{\varepsilon(p)}\,\lambda`$,
i.e.

$$\overline{\lambda} \\;=\\; \varepsilon(p)^{-1}\\,\lambda.$$

So the Hecke eigenvalue of a nebentypus eigenform is **not** real in general; it
is real up to the root of unity $`\varepsilon(p)`$. For trivial nebentypus,
$`\lambda`$ is real — the classical self-adjointness of $`T_p`$ on
$`S_k(\Gamma_0(N))`$. This is the first consumer: the conjugation relation
`conj_heckeEigenvalue_eq_of_hasNebentypus`, which the Deligne–Serre lifting
uses to control the eigenvalues of the mod-$`\ell`$ Galois representation
against the complex ones.

### 6.2 Normality and the nebentypus eigenbasis

Two further facts complete the spectral picture.

* **Commutativity.** The operators $`T_p`$ ($`p \nmid N`$) commute with each
  other and with the diamond operators: they form the (commutative) Hecke
  algebra of the double cosets, and the diamond operators act by the
  nebentypus character on each component.
* **Normality.** By §4, $`T_p^* = \overline{\varepsilon(p)}\,T_p`$, so
  $`T_p T_p^* = T_p^* T_p`$: each $`T_p`$ is normal. The diamond operators are
  unitary (a slash by an element of $`\mathrm{SL}_2(\mathbb{Z})`$ preserves the
  Petersson product), hence also normal.

A commuting family of normal operators on a finite-dimensional complex inner
product space is simultaneously diagonalizable (the complex spectral theorem);
applying this to the Hecke algebra on $`S_k(\Gamma_1(N))`$ gives a basis of
simultaneous eigenforms for all the diamond operators and all $`T_p`$ with
$`p \nmid N`$. Each basis vector lies in some nebentypus component, because it
is an eigenvector for the diamond operators. This is the second consumer, the
existence of a **nebentypus eigenbasis**, `exists_basis_hasNebentypus_qCoeff_hecke_eigen`:
a basis $`b_1, \dots, b_n`$ of $`S_k(\Gamma_1(N))`$ in which every $`b_i`$ has
a nebentypus $`\varepsilon_i`$ and is a simultaneous $`q`$-coefficient Hecke
eigenform. (For a normalized eigenform, the eigenvalue $`\lambda_p`$ is just
the coefficient $`a_p`$.)

### 6.3 Why Deligne–Serre need it

The weight-one lifting of Deligne–Serre starts with a normalized weight-one
eigenform $`f`$ and builds its Artin representation from the Hecke eigenvalues:
$`\mathrm{tr}\,\rho_f(\mathrm{Frob}_p) = a_p`$ and
$`\det\rho_f(\mathrm{Frob}_p) = \varepsilon(p)`$. Two steps need the
adjointness. First, the eigenvalues must be compared with their complex
conjugates — the conjugation relation of §6.1 says the comparison is controlled
by $`\varepsilon(p)`$, which is exactly the determinant of the representation.
Second, the modular form itself is extracted from a Hecke-stable space; the
eigenbasis of §6.2 is what guarantees that the space has a basis of forms with
well-defined eigenvalues and nebentypus, and hence that the Galois
representation can be read off coefficient by coefficient. In the FLT column,
the first is
`CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus` and the second is
`CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen`; both sit directly
under the weight-one theorem of [019](019-deligne-serre-weight-one.md), and the
node proved here is the leaf their proofs rest on.

## 7. Lean summary

### 7.1 The statement

The port states the theorem with the convention of §2 and the operator of §3:

```lean
theorem CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus
    (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) (f g : CuspForm (Gamma1 N) k) (hf : CuspForm.HasNebentypus ε f)
    (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.peterssonOn (Gamma1 N) k
        (heckeU k p ⇑f + ε (p : ZMod N) • (⇑f ∣[k] heckeDiagMatrix p)) ⇑g
      = starRingEnd ℂ (ε (p : ZMod N)) *
        CuspForm.peterssonOn (Gamma1 N) k ⇑f
          (heckeU k p ⇑g + ε (p : ZMod N) • (⇑g ∣[k] heckeDiagMatrix p))
```

([`PeterssonHeckeTheorems.lean`](https://github.com/htzh/flt_for_human/blob/2d8e5c1/lean/FLTForHuman/ModularForms/Analytic/PeterssonHeckeTheorems.lean#L25-L37);
the pin's statement authority is
[`Thm_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean)).
Here `heckeU k p f` is §3's `U_p`, `heckeDiagMatrix p` is `diag(p,1)`, and
`starRingEnd ℂ` is complex conjugation.

### 7.2 The definition layer

The product is the pin's `peterssonOn`, a three-line wrapper over mathlib's
pointwise density (`UpperHalfPlane.petersson`):

```lean
def peterssonOnIntegrand (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) : ℂ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ Γ,
    UpperHalfPlane.petersson k (f ∣[k] (q.out⁻¹ : SL(2, ℤ))) (g ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ

def peterssonOn (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ) : ℂ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
    (peterssonOnIntegrand Γ k f g)
```

([`Petersson.lean`](https://github.com/htzh/flt_for_human/blob/2d8e5c1/lean/FLTForHuman/ModularForms/Analytic/Petersson.lean)).
`ModularGroup.fd` is the standard fundamental domain $`\mathcal{D}`$; the
`finsum` over the quotient is the coset sum of §2. The proof's other definition
layer is the fundamental-domain ground — `goodSet`, the set of points at which
exactly two translates of $`\mathcal{D}`$ meet, and the double-counting
identities for integrals over $`\mathcal{D}`$ —
[`ModularFundamentalDomain.lean`](https://github.com/htzh/flt_for_human/blob/2d8e5c1/lean/FLTForHuman/AutomorphicForm/UpperHalfPlane/ModularFundamentalDomain.lean).

### 7.3 The engine

The 118-declaration development is the tier-3 engine
[`PeterssonHecke.lean`](https://github.com/htzh/flt_for_human/blob/2d8e5c1/lean/FLTForHuman/ModularForms/Analytic/PeterssonHecke.lean),
in namespace `CuspForm.PetHeckeAdj`. The names corresponding to §5 are:

| §5 | engine |
|---|---|
| the $`p+1`$ representatives, $`\Lambda`$ | `Lam`, `rr`, `exists_rr_mul_mem`, `rr_mul_rr_inv_mem` |
| the unfolding | `unfold_sum` |
| $`\Phi`$, $`\Psi`$ | `Φ`, `Ψ` |
| the character identity §5.3 | `slash_heckeDiagMatrix_eq`, `Ψ_eq`, `norm_char_p` |
| the two integrands | `integrand_left`, `integrand_right` |
| the integral invariance | `integral_cosum_pair`, `adm_slash_α`, `adm_coe` |
| assembly | `main` |

The engine is unlisted (tier 3) and registered in
[`UNWIRED-PUBLIC.md`](https://github.com/htzh/flt_for_human/blob/2d8e5c1/lean/spec/UNWIRED-PUBLIC.md)
with all 118 declarations and their pin originals; the tier-1 façade above is
the only wired declaration, and it is the one-line application of `main`.

### 7.4 Verification

* The four modules build with 0 errors and 0 warnings;
  `#print axioms CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus` is
  `[propext, Classical.choice, Quot.sound]`; there is no `sorry`.
* The checker reads **9877 identical, 0 mismatched, 0 missing**; this node's
  wired surface is the headline (+1), the `peterssonOn` definitions (+3) and the
  fundamental-domain ground (+16).
* The engine's 118 statements were additionally diffed against the pin's
  `S_` file by last name: 118/118 equal.
* The deferred surface — the pin's exact-volume/L2 chain
  (`Gamma0ExactVolume`, `FundamentalDomainExactVolume`, `EisensteinScattering`,
  `L2ProductionInstance`, `L2AutomorphicCarrier`, `TruncatedDomainPartition`)
  and the four "gate" theorems of the fundamental-domain module — is registered
  in [`CARRY-FORWARD.md`](https://github.com/htzh/flt_for_human/blob/2d8e5c1/lean/CARRY-FORWARD.md);
  no needed D-S node imports that chain directly.

The full port record, with the build measurements and the `v4.34.0` API
adaptations, is
[../lean/topics/deligneSerre/TOPIC-petersson-hecke-adjointness.md](../lean/topics/deligneSerre/TOPIC-petersson-hecke-adjointness.md).

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts
  in Mathematics **228**, Springer, 2005 — §5.2–5.5: the Hecke operators, the
  Petersson product, and Theorem 5.5.3, the adjointness of §4.
* T. Miyake, *Modular Forms*, Springer, 1989 — §4.5, the same adjointness in
  the classical normalization.
* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*,
  Princeton University Press, 1971 — Proposition 3.39.
* [P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. Éc.
  Norm. Supér. (4) **7** (1974), 507–530](https://www.numdam.org/item/ASENS_1974_4_7_4_507_0/) —
  the weight-one theorem of §6.3.
