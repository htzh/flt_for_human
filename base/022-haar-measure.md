# Haar measure: invariance, unimodularity, and convolution on the adeles

Twenty-second of the `base/` notes. [012](012-adeles-and-automorphic-representations.md)
introduced the adele ring, $`\mathrm{GL}_2(\mathbb{A}_F)`$ and the compact-open subgroups
$`K_0(N)`$, and [019](019-stichtenoth-genus-and-the-adelic-index.md) used adelic *counting*
on a function field. Neither note said what measure the adelic integrals are taken
against. The port topic
[lean/topics/automorphicForm/TOPIC-rightConv-comm.md](../lean/topics/automorphicForm/TOPIC-rightConv-comm.md)
is written entirely in that measure: its headline says two smoothing operators commute,
its first reduction turns the statement into a kernel identity, its reduced statement
lives on a pushed-forward measure, and — as the topic's §1 records — the only cited theorem
premise of the two rows is that the Haar measure on $`\mathrm{GL}_2(\mathbb{A}_F)`$ is
*right*-invariant.

This note supplies the mathematics behind those moves. The mathematics is §1–§9; §10 is
the Lean map (names, files, and the encoding walls the topic file assumes). The source of
truth throughout is the port's own Haar layer, written against mathlib `v4.34.0`:

- `NumberTheory/AdelicHaar/{Local,Adele,GeneralLinear,MulRightInvariant}.lean` — the
  adelic measure and its right-invariance;
- `RepTheory/{ProjectedHaar,AntiInvolutionHaar}.lean` — the generic convolution engine;
- `AutomorphicForm/Adelic/RightConvComm/{Frame,MeasureAssembly,SliceCentrality}.lean` —
  the adelic instantiation.

Citations are pinned at `htzh/flt_for_human@1995556` for the port,
`anthropics/fermats-last-theorem@aa2d8b3` for the pin, and mathlib at tag `v4.34.0` (the
tag the port's `lake-manifest.json` resolves to).

## 1. A measure that translations do not change

### 1.1 Invariance

Let $`G`$ be a locally compact Hausdorff topological group, with its Borel
$`\sigma`$-algebra. For a Borel measure $`\mu`$ on $`G`$ and $`g \in G`$, left translation
$`L_g(x) = gx`$ acts on measures by pushforward, and left invariance says

$$(L_g)_\ast \mu = \mu \quad\text{for all } g,
\qquad\text{i.e.}\qquad \mu(gE) = \mu(E)$$

for every $`g`$ and every measurable $`E`$. In integral form this is the change of
variables

$$\int_G f(gx) \\, d\mu(x) = \int_G f(x) \\, d\mu(x),$$

and it is equivalent to $`\int_G f(g^{-1}x) \, d\mu(x) = \int_G f(x) \, d\mu(x)`$. Right
invariance is the same statement for $`R_g(x) = xg`$:

$$(R_g)_\ast \mu = \mu,
\qquad\text{i.e.}\qquad \mu(Eg) = \mu(E).$$

The two are *different* conditions, and §2 is about the difference. Everything the topic
file does with the measure — every substitution, every Fubini swap, every conjugation —
is one of these two identities in disguise.

### 1.2 Existence and uniqueness

**Theorem (Haar).** Every locally compact Hausdorff topological group carries a nonzero
left-invariant Radon measure, and any two are positive multiples of one another.

The existence proof (Gleason; the form mathlib follows) is worth recalling because it
explains the normalization. For compact $`K`$ and a neighbourhood $`U`$ of $`1`$, let
$`(K : U)`$ be the least number of left translates of $`U`$ needed to cover $`K`$, and put
$`h_U(K) = (K : U)/(K_0 : U)`$ for a fixed compact $`K_0`$ with nonempty interior. As
$`U`$ shrinks to $`\{1\}`$, the functions $`h_U`$ live in the compact product
$`\prod_K [0, (K : K_0)]`$; Tychonoff gives a limit point $`h`$, which is a content —
finitely additive, monotone, and invariant under left translation on compact sets. The
associated outer measure restricts to a Borel measure $`\mu`$ with $`\mu(K_0) = 1`$. So
existence comes with *one* normalization chosen by hand; nothing else about the
construction is used downstream.

Uniqueness is what makes the measure canonical up to scale. If $`\mu`$ is a left Haar
measure and $`\nu`$ is any nonzero left-invariant measure finite on compacts, then for
every $`f \in C_c(G)`$ with $`f \ge 0`$ and $`f \neq 0`$ the ratio
$`\int f \, d\nu \big/ \int f \, d\mu`$ is independent of $`f`$, and

$$\nu = c \\, \mu, \qquad c = \frac{\int_G f \\, d\nu}{\int_G f \\, d\mu}.$$

The proof is a two-line Fubini computation: for $`\mu`$ left-invariant and $`\rho`$
right-invariant, one has

$$\int_G f \\, d\mu \cdot \int_G h \\, d\rho
  = \int_G h \\, d\mu \cdot \int_G f \\, d\rho
\qquad (f, h \in C_c(G)),$$

by writing both sides as an integral over $`G \times G`$ against
$`d\mu(x)\, d\rho(y)`$ and substituting $`(x, y) \mapsto (xy, y)`$ on one side. The constant
is mathlib's `haarScalarFactor`.

### 1.3 What the measure looks like in the examples that matter

| group | left Haar measure |
|---|---|
| $`\mathbb{R}^n`$ additive | Lebesgue measure $`dx`$ |
| $`\mathbb{R}^\times`$ | $`dx/\lvert x \rvert`$ |
| compact $`G`$ | any nonzero invariant measure; normalized to total mass $`1`$ |
| discrete $`G`$ | counting measure |
| local field $`K_v`$ (additive) | normalized by $`\mu(\mathcal{O}_v) = 1`$ |
| $`K_v^\times`$ | normalized by $`\mu(\mathcal{O}_v^\times) = 1`$, so $`d^\times x = \lvert x \rvert^{-1} dx`$ up to the standard factor |
| product $`G_1 \times G_2`$ | $`\mu_1 \otimes \mu_2`$ |

Two of these deserve a remark.

*The local normalizations are the reason adelic measure theory is well posed.* At each
finite place the ring of integers $`\mathcal{O}_v`$ is compact and open, so it is the
natural unit of volume; the product over all places of the local measures is then
well defined on the restricted product. The pin never constructs that product: it takes
the adele ring $`\mathbb{A}_F`$ and $`\mathrm{GL}_2(\mathbb{A}_F)`$ as locally compact
Hausdorff groups and invokes Haar existence (§7).

*Additive and multiplicative Haar measures are different objects.* The adele ring is a
locally compact Hausdorff topological ring, so its additive group has an additive Haar
measure (`adelicAddHaar`); $`\mathrm{GL}_2(\mathbb{A}_F)`$ is a locally compact Hausdorff
topological group in its own right, so it has a multiplicative one
(`adelicGLHaar`). The topic integrates against the second. The additive measure is what
the box and Siegel volumes of the definitional layer measure.

## 2. Left versus right: the modular character

Fix a left Haar measure $`\mu`$. For fixed $`g`$, the right translate $`(R_g)_\ast \mu`$ is
again left-invariant, because right and left translations commute:

$$(R_g)_\ast \mu(hE) = \mu(hEg) = \mu(Eg) = (R_g)_\ast \mu(E).$$

It is finite on compacts ($`R_g`$ is a homeomorphism) and positive on nonempty open
sets, so by uniqueness there is a unique positive real number $`\Delta_G(g)`$ with

$$(R_g)_\ast \mu = \Delta_G(g) \\, \mu,
\qquad\text{i.e.}\qquad \mu(Eg) = \Delta_G(g) \\, \mu(E).$$

The number does not depend on the choice of $`\mu`$ (rescaling $`\mu`$ rescales both
sides). The function

$$\Delta_G : G \longrightarrow \mathbb{R}_{\gt 0}$$

is the **modular character**. It is a continuous group homomorphism:

- $`\Delta_G(gh) = \Delta_G(g)\Delta_G(h)`$, because $`R_{gh} = R_h \circ R_g`$;
- $`\Delta_G(aha^{-1}) = \Delta_G(h)`$, because the target is abelian;
- $`\Delta_G(g^{-1}) = \Delta_G(g)^{-1}`$;
- continuity follows by testing on a fixed compact set of positive finite measure.

The group is **unimodular** when $`\Delta_G \equiv 1`$, equivalently when every left Haar
measure is right-invariant, equivalently when the left and right Haar measures coincide.
Unimodular groups include abelian groups; compact groups (if $`\mu(G) \lt \infty`$ then
$`\Delta_G(g)\mu(G) = \mu(G)`$); discrete groups; nilpotent groups; connected semisimple
groups; and $`\mathrm{GL}_n(k)`$ for $`k`$ a local field. The adelic group
$`\mathrm{GL}_2(\mathbb{A}_F)`$ is unimodular as well, but the port proves it directly by
an elementary argument over the adele ring rather than by assembling the local cases;
§3 gives that proof.

**Inversion.** Put $`\mu^{\mathrm{inv}} := (\mathrm{inv})_\ast \mu`$, so
$`\mu^{\mathrm{inv}}(E) = \mu(E^{-1})`$. If $`\mu`$ is a left Haar measure then
$`\mu^{\mathrm{inv}}`$ is a *right* Haar measure:

$$\mu^{\mathrm{inv}}(Eg) = \mu\bigl((Eg)^{-1}\bigr) = \mu(g^{-1}E^{-1}) = \mu(E^{-1})
  = \mu^{\mathrm{inv}}(E).$$

If $`\mu`$ is unimodular then $`\mu^{\mathrm{inv}}`$ is also left-invariant: the third
equality above becomes valid with $`g^{-1}E^{-1}`$ replaced by $`E^{-1}g^{-1}`$ and
right-invariance of $`\mu`$. Hence $`\mu^{\mathrm{inv}} = c\,\mu`$ by uniqueness, and
applying inversion twice gives $`\mu = c^2 \mu`$; testing on a compact set of positive
finite measure gives $`c^2 = 1`$, so $`c = 1`$. Therefore

> a left Haar measure is inversion-invariant if and only if the group is unimodular.

This little argument — a measure-preserving involution, plus uniqueness, forces the
scale to be a positive square root of $`1`$ — is the prototype of the anti-involution
lemma of §4.4 and is repeated verbatim in the code.

## 3. Why $`\mathrm{GL}_2(\mathbb{A}_F)`$ is unimodular

This is the mathematical content of the topic's one cited theorem premise,
`NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar`. The proof is elementary linear
algebra over a ring once one input from arithmetic is granted.

Let $`A`$ be a commutative ring and $`G = \mathrm{GL}_2(A)`$; in the application
$`A = \mathbb{A}_F`$. Write

$$E(x) = \begin{pmatrix} 1 & x \\\\ 0 & 1 \end{pmatrix}, \qquad
  L(y) = \begin{pmatrix} 1 & 0 \\\\ y & 1 \end{pmatrix}, \qquad
  D(u, e) = \begin{pmatrix} u & 0 \\\\ 0 & e \end{pmatrix} \quad (u, e \in A^\times),$$

and $`w = [[0,1],[1,0]]`$,
$`s = [[-1,0],[0,1]]`$.

**Step 1: elementary and diagonal matrices have trivial modular character.**

$$s \\, E(x) \\, s^{-1} = E(x)^{-1}, \qquad s \\, L(y) \\, s^{-1} = L(y)^{-1}.$$

Since $`\Delta_G`$ is conjugation-invariant, $`\Delta_G(E(x))^2 = 1`$ and
$`\Delta_G(L(y))^2 = 1`$; both are positive reals, so both equal $`1`$. Likewise
$`w\,D(u,1)\,w^{-1} = D(1,u)`$, so $`\Delta_G(D(u,1)) = \Delta_G(D(1,u))`$, while
$`D(u,1)D(1,u) = D(u,u) = uI`$ is central, so
$`\Delta_G(D(u,1))\Delta_G(D(1,u)) = 1`$. Hence
$`\Delta_G(D(u,1))^2 = 1`$, so $`\Delta_G(D(u,1)) = 1`$, and then
$`\Delta_G(D(u,e)) = \Delta_G(D(u,1))\Delta_G(D(1,e)) = 1`$.

**Step 2: any matrix with an invertible $`(0,0)`$-entry has trivial modular character.**
For $`h = [[a,b],[c,d]]`$ with $`a \in A^\times`$,

$$h = L\bigl(ca^{-1}\bigr) \\, D\bigl(a, a^{-1}\det h\bigr) \\, E\bigl(a^{-1} b\bigr).$$

(Multiply out: the first two factors give
$`[[a,0],[c,a^{-1}\det h]]`$; multiplying by $`E`$ fills
in $`b`$ and the correct lower-right entry $`c a^{-1} b + a^{-1}(ad - bc) = d`$.) All three
factors on the right have $`\Delta_G = 1`$ by Step 1, so $`\Delta_G(h) = 1`$.

**Step 3 (the arithmetic input): $`A = \mathbb{A}_F`$ has stable range $`1`$.** That is:
for all $`a, c \in A`$ there is $`x \in A`$ with $`a + xc \in A^\times`$. The proof is
componentwise, over the two factors of
$`\mathbb{A}_F = \mathbb{A}_{F,\infty} \times \mathbb{A}_{F,\mathrm{fin}}`$, and uses only
that units are detected componentwise.

- *Finite adeles.* An element of $`\mathbb{A}_{F,\mathrm{fin}} = \prod'_v K_v`$ is a unit
  iff every component is a unit. Suppose $`ad - bc`$ is a unit. At a finite place $`v`$,
  the row $`(a_v, c_v)`$ is unimodular in the local field $`K_v`$; if $`a_v`$ is a unit take
  $`x_v = 0 \in \mathcal{O}_v`$, otherwise $`c_v`$ must be a unit and
  $`x_v = 1 \in \mathcal{O}_v`$ works. Then $`x = (x_v)_v`$ is an *integral* adele — each
  component lies in $`\mathcal{O}_v`$, so $`x`$ lies in the restricted product — and
  $`a + xc`$ is a unit at every finite place.
- *Infinite adeles.* An element of $`\mathbb{A}_{F,\infty} = \prod_{v \mid \infty} K_v`$
  is a unit iff every component is nonzero. At a place $`v`$, if $`a_v \neq 0`$ take
  $`x_v = 0`$; otherwise $`a_v d_v - b_v c_v = -b_v c_v \neq 0`$, so $`c_v \neq 0`$ and
  $`x_v = 1`$ gives $`a_v + x_v c_v = c_v \neq 0`$.

**Step 4: conclusion.** Let $`g \in G`$ be arbitrary; its determinant is a unit. Choose
$`x`$ with $`a + xc \in A^\times`$, where $`a, c`$ are the entries of $`g`$. The matrix
$`E(x)g`$ has entry $`a + xc`$ in position $`(0,0)`$, so $`\Delta_G(E(x)g) = 1`$ by Step 2,
and $`\Delta_G(E(x)) = 1`$ by Step 1. Therefore $`\Delta_G(g) = 1`$. Since $`g`$ was
arbitrary, $`\Delta_G \equiv 1`$:

> the Haar measure on $`\mathrm{GL}_2(\mathbb{A}_F)`$ is both left- and right-invariant,
> and (by §2) inversion-invariant.

Three remarks. First, the argument is not special to $`\mathrm{GL}_2`$ or to the adeles:
with the evident $`n \times n`$ generators in place of $`E, L, D`$, the same proof shows
that $`\mathrm{GL}_n(A)`$ is unimodular for any ring $`A`$ of stable range $`1`$.
Second, the only place the number theory enters is Step 3, and it enters twice in
different ways — the ultrametric local argument at the finite places, where the
correction term can be taken integral, and the elementary case split at the infinite
places. Third, compactness and openness of the level subgroups — central to §5 and to
the whole topic — play no role in unimodularity.

## 4. Convolution against a Haar measure

### 4.1 The two operators

For functions $`f, h : G \to \mathbb{C}`$ and a measure $`\mu`$, the standard convolution
is

$$(f \ast h)(x) = \int_G f(y) \\, h(y^{-1}x) \\, d\mu(y).$$

The topic's two operators are this convolution and a right-regular pairing of it. The
port's `rightConv` (its `rc`) is

$$(\varphi \star f)(g) = \int_G \varphi(gx) \\, f(x) \\, d\mu(x),$$

and `convKer` is the convolution itself:

$$\mathrm{convKer}_\mu(P, Q)(x) = \int_G P(y) \\, Q(y^{-1}x) \\, d\mu(y) = (P \ast Q)(x).$$

In the topic, $`\varphi`$ is an automorphic function, $`f`$ a level-spherical test
function, $`h`$ a factorizable test function, and $`\mu`$ is `adelicGLHaar`. The headline
$`(\varphi \star f) \star h = (\varphi \star h) \star f`$ is reduced (§8) to the kernel
identity

$$h \ast f = f \ast h, \qquad\text{i.e.}\qquad
  \mathrm{convKer}_\mu(h, f) = \mathrm{convKer}_\mu(f, h).$$

### 4.2 Left invariance is what makes convolution associative

Compute $`((f \ast g) \ast h)(x)`$ and substitute $`z = yw`$ in the inner variable:

$$((f \ast g) \ast h)(x)
  = \int_y \int_z f(y) g(y^{-1}z) h(z^{-1}x) \\, d\mu(z) \\, d\mu(y)
  \\;\overset{z = yw}{=}\\; \int_y \int_w f(y) g(w) h\bigl((yw)^{-1}x\bigr)
    \\, d\mu(w) \\, d\mu(y),$$

where $`d\mu(z) = d\mu(yw) = d\mu(w)`$ is exactly left invariance. The last expression
is $`(f \ast (g \ast h))(x)`$. So:

> associativity of convolution is left invariance of the measure, and nothing else.

The port's `KernelReduction.rc_mul` is this substitution in one variable:
$`(\varphi \star f)(gy) = \int \varphi(gx) f(y^{-1}x) \, d\mu(x)`$.

The right-regular pairing is the convolution of $`\varphi`$ with the reflected function
$`f^\vee(x) = f(x^{-1})`$. Indeed, substituting $`y = gv`$ (again left invariance),

$$\mathrm{convKer}_\mu(\varphi, f^\vee)(g)
  = \int_y \varphi(y) f\bigl((y^{-1}g)^{-1}\bigr) \\, d\mu(y)
  = \int_y \varphi(y) f(g^{-1}y) \\, d\mu(y)
  = \int_v \varphi(gv) f(v) \\, d\mu(v) = (\varphi \star f)(g).$$

### 4.3 Fubini: the re-association

With $`\varphi, f, h`$ continuous and $`f, h`$ compactly supported, the integrand on
$`G \times G`$ is continuous and compactly supported, hence integrable; Fubini applies
and

$$((\varphi \star f) \star h)(g)
  = \int_y \Bigl(\int_x \varphi(gx) f(y^{-1}x) \\, d\mu(x)\Bigr) h(y) \\, d\mu(y)
  = \int_x \varphi(gx) \Bigl(\int_y f(y^{-1}x) h(y) \\, d\mu(y)\Bigr) d\mu(x)
  = (\varphi \star \mathrm{convKer}_\mu(h, f))(g).$$

This is the port's `KernelReduction.rc_rc`, and it is the topic's §2.2: the last three
lines of each `solution` are exactly this re-association. Continuity and compact support
are not decoration — they are the hypotheses that make the double integral an honest
product integral over a compact set.

### 4.4 The symmetry of the kernel

Everything above works for any left Haar measure. What is not automatic is

$$\mathrm{convKer}_\mu(P, Q) = \mathrm{convKer}_\mu(Q, P);$$

on a nonabelian group the two differ by the order of the factors, and the topic's whole
proof is about producing this equality for the two particular test functions. Two
mechanisms produce it, and the topic uses both.

**A measure-preserving anti-involution.** Let $`\theta : G \to G`$ be a continuous
anti-involution: $`\theta(xy) = \theta(y)\theta(x)`$, $`\theta^2 = \mathrm{id}`$, and
suppose $`\theta`$ preserves the measure, $`\theta_\ast \nu = \nu`$. Then

$$\mathrm{convKer}_\nu(P, Q)(\theta x)
  = \mathrm{convKer}_\nu(Q \circ \theta, P \circ \theta)(x),$$

by substituting $`y \mapsto \theta(y)`$ and using $`\theta_\ast\nu = \nu`$ and
inversion-invariance. If in addition $`\theta x = k x k^{-1}`$ for some $`k`$ under which
$`P`$ and $`Q`$ are conjugation-invariant, and if $`\nu`$ is both left- and
right-invariant, then the kernel is conjugation-invariant and

$$\mathrm{convKer}_\nu(P, Q)(x) = \mathrm{convKer}_\nu(P, Q)(\theta x)
  = \mathrm{convKer}_\nu(Q, P)(x).$$

The port's `AntiInvolutionHaar.convKer_comm` is this statement; `convKer_conj` uses both
left and right invariance, and `convKer_θ` uses inversion-invariance.

**Why $`\theta_\ast\nu = \nu`$ holds.** Suppose $`\nu`$ is a left Haar measure that is
also right-invariant. If $`\theta`$ is an anti-involution then $`\theta_\ast\nu`$ is again
left-invariant:

$$\theta_\ast\nu(hE) = \nu\bigl(\theta(hE)\bigr) = \nu\bigl(\theta(E)\theta(h)\bigr)
  = \nu\bigl(\theta(E)\bigr) = \theta_\ast\nu(E),$$

the middle equality being right-invariance of $`\nu`$, with the factor $`\theta(h)`$ on
the right. Left-invariance alone is not enough here: the factor $`\theta(h)`$ sits on the
right of $`\theta(E)`$, so only right-invariance can absorb it. This is exactly why the
topic's hypotheses carry right-invariance of the archimedean measure, and why §3 is
needed at all in this part of the argument. The pushforward is finite on compacts
because $`\theta`$ is a homeomorphism and positive on open sets, so it is a left Haar
measure, and $`\theta_\ast\nu = c\,\nu`$ by uniqueness; $`\theta^2 = \mathrm{id}`$ gives
$`\nu = c^2 \nu`$, and testing on a compact set of positive finite measure gives
$`c = 1`$. This is the $`c^2 = 1`$ argument of §2 again, now for a general
anti-involution; for $`\theta = \mathrm{inv}`$ it recovers inversion-invariance, and for
the place-wise anti-involution `thetaArch` of the archimedean
adeles it gives $`(\theta_\mathrm{Arch})_\ast \nu = \nu`$.

## 5. Pushing Haar measure forward: the projected measure $`\nu`$

### 5.1 The frame is a product

The engine of the topic abstracts the adelic group as a **frame**: group homomorphisms

$$\pi : G \to A, \qquad \pi_f : G \to B, \qquad \iota : A \to G, \qquad \iota_f : B \to G$$

with $`\pi \iota = \mathrm{id}_A`$, $`\pi_f \iota_f = \mathrm{id}_B`$,
$`\pi_f \iota = 1`$, $`\pi \iota_f = 1`$, and the **separation** axiom

$$\pi x = \pi y \ \wedge\ \pi_f x = \pi_f y \ \Longrightarrow\ x = y.$$

For the adelic group, $`A = \mathrm{GL}_2(\mathbb{A}_{F,\infty})`$,
$`B = \mathrm{GL}_2(\mathbb{A}_{F,\mathrm{fin}})`$, $`\pi`$ and $`\pi_f`$ are the two
projections `glArch`/`glFin`, and separation is
`AdelicLevel.eq_of_glArch_eq_of_glFin_eq`: the adelic group *is* the fibre product of its
two projections.

Separation upgrades to a group isomorphism
$`G \cong A \times B`$, $`x \mapsto (\pi x, \pi_f x)`$, with inverse
$`(a, b) \mapsto \iota(a)\iota_f(b)`$. That the two orders of the sections agree is
checked by separation, and continuity in both directions is part of the hypotheses
below. So the frame is a product, split into its archimedean and finite parts.

Against a frame and a subgroup $`U_f \le B`$ the engine builds

- the **slab** $`S = \pi_f^{-1}(U_f)`$, which under the isomorphism is $`A \times U_f`$;
- the **level** subgroup $`\mathrm{ker}\,\pi \cap \pi_f^{-1}(U_f) = \{1\} \times U_f`$;
- the **slice** of a function $`h`$ by $`u \in G`$: $`a \mapsto h(\iota(a)\iota_f(\pi_f u))`$;
- the **cut** $`\mathbf{1}_S \cdot (f_a \circ \pi)`$ of an archimedean function $`f_a`$;
- the **pushed-forward measure** $`\nu = (\mu \restriction S) \circ \pi^{-1}`$ on $`A`$,
  i.e. $`\nu(C) = \mu(\pi^{-1}(C) \cap S)`$.

### 5.2 When is $`\nu`$ a Haar measure?

**Claim.** If $`\mu`$ is a Haar measure on $`G \cong A \times B`$, then $`\mu`$ is a
positive multiple of $`\mu_A \otimes \mu_B`$ for Haar measures $`\mu_A, \mu_B`$ on the
factors; consequently

$$\nu = c \\, \mu_B(U_f) \\, \mu_A .$$

*Proof.* The product of two Haar measures is a Haar measure on the product (left
invariance is componentwise), so uniqueness (§1.2) gives
$`\mu = c (\mu_A \otimes \mu_B)`$. Restricting to $`S = A \times U_f`$ and pushing forward
along the first projection gives $`c (\mu_A \otimes (\mu_B \restriction U_f))`$ mapped to
$`c\,\mu_B(U_f)\,\mu_A`$. $`\square`$

Since $`c \gt 0`$ and $`\mu_A`$ is Haar, the claim says:

- $`\nu`$ is left-invariant, always;
- $`\nu \neq 0`$ (positive on nonempty open sets) iff $`\mu_B(U_f) \gt 0`$; a sufficient
  condition is that $`U_f`$ is open and nonempty, since a Haar measure gives positive
  mass to every nonempty open set;
- $`\nu`$ is finite on compacts iff $`\mu_B(U_f) \lt \infty`$; a sufficient condition is
  that $`U_f`$ is compact, or more generally relatively compact.

These two sufficient conditions are exactly the two hypotheses of the port's
`ProjectedHaar.nu_isHaarMeasure`: `IsCompact (Uf : Set B)` and `IsOpen (slab Φ Uf)`. The
proof in the code checks the three fields of Haar directly rather than factoring through
the product description, but the mathematics is the display above.

Two more invariance properties come for free:

- $`\nu`$ is right-invariant as soon as $`\mu`$ is: right translation on $`A`$ corresponds
  under the isomorphism to right translation by $`\iota(a)`$, and
  $`\pi_f(\iota(a)) = 1`$ keeps $`S`$ stable. So a *unimodular* $`\mu`$ gives a
  right-invariant $`\nu`$. This is where §3 enters the engine.
- $`\nu`$ is inversion-invariant when $`\mu`$ is (combine right-invariance with §2).

### 5.3 The adelic instance

For $`G = \mathrm{GL}_2(\mathbb{A}_F)`$, $`U_f = \mathrm{glFin}(U)`$ for a subgroup
$`U \le G`$, and $`\mu`$ the adelic Haar measure `adelicGLHaar`, the pushed-forward
measure is

$$\texttt{archNu}(U) = \nu, \qquad\text{a measure on } \mathrm{GL}_2(\mathbb{A}_{F,\infty}).$$

Haar-ness requires `IsCompact (glFin '' U)` and `IsOpen (glFin '' U)`. In the level-$`N`$
specialization $`U = \texttt{levelOne}(N) \cap \mathrm{GL}_2(\widehat{\mathcal{O}}_F)`$,
so $`\mathrm{glFin}(U) = \texttt{finiteLevelOne}(N)`$, whose compactness and openness
(openness needs $`N \neq 0`$) are the side facts the plain silo proves. Right-invariance
of $`\nu`$ uses §3, and inversion-invariance follows.

### 5.4 What the engine does with $`\nu`$

The measure-theoretic content of the reduction is this. A level-spherical $`f`$ is, by
construction, a cut function $`\mathbf{1}_S (f_a \circ \pi)`$. Convolving it against a
function $`h`$ that is invariant under the level, and pushing the integral from $`G`$ to
$`A`$, replaces

- the ambient measure $`\mu`$ by the projected $`\nu`$, which §5.2 shows is *again a Haar
  measure*;
- the cut function by the slice of $`h`$;
- the two-sided invariance of $`h`$ by $`\{1\} \times U_f`$ becomes the identity that
  identifies the slice.

That is the port's `ProjectedHaar.convKer_cut_comm`: the ambient kernel identity holds as
soon as the projected identity holds on every slice. The problem is thereby pushed onto
the archimedean group, with the level folded into $`\nu`$. Compactness of $`U_f`$ is what
makes $`\nu`$ Radon; openness is what keeps it nonzero. Nothing else about the level
survives the pushforward.

## 6. The quotient Haar measure: $`\mathrm{PGL}_2`$

One more Haar measure sits in the same layer and the same topic (its §4.2, wave W2). The centre
$`Z = \{uI : u \in \mathbb{A}_F^\times\}`$ is a closed normal subgroup of
$`\mathrm{GL}_2(\mathbb{A}_F)`$: closed because $`G`$ is Hausdorff and $`Z`$ is an
intersection of closed equalizers $`\{z : gz = zg\}`$, normal because it is central. The
projective linear group

$$\mathrm{PGL}_2(\mathbb{A}_F) = \mathrm{GL}_2(\mathbb{A}_F) / Z$$

is a locally compact Hausdorff topological group, so it carries a Haar measure
(`adelicPGLHaar`) — the measure the cusp carriers and the Siegel-volume node integrate
over. Two facts about it are used, and both are the standard behaviour of the quotient
map $`\mathrm{mk} : G \to G/Z`$:

- $`\mathrm{mk}`$ is open, so the image of a nonempty open set has positive measure;
- $`\mathrm{mk}`$ is continuous, so the image of a compact set is compact and has finite
  measure.

Mathlib's quotient-measure theory (`MeasureTheory.QuotientMeasureEqMeasurePreimage`)
constructs the quotient measure from a fundamental domain; the port does not need it,
because $`G/Z`$ is already a group to which `Measure.haar` applies.

## 7. What is, and is not, formalized

It is worth being explicit about which of the mathematics above is mathlib and which is
the port's, because the topic file leans on the distinction.

- **Existence and uniqueness of Haar measure** are mathlib theorems
  (`MeasureTheory.Measure.haar`, `haarMeasure_unique`, `haarScalarFactor`). The port
  *defines* `adelicGLHaar` as `Measure.haar` on $`\mathrm{GL}_2(\mathbb{A}_F)`$ and
  `adelicAddHaar` as `Measure.addHaar` on $`\mathbb{A}_F`$. The local measures of §1.3 and
  the restricted-product construction are **not** formalized; only the abstract measure
  on the adelic group is.
- **Normalization is arbitrary.** `Measure.haar` is
  `haarMeasure (Classical.arbitrary _)`, so the chosen measure has no canonical
  normalization, and integrals have no canonical numerical value. Every statement the
  topic uses is an *invariance* statement, which is independent of the choice; no
  measure of a concrete set and no value of an integral appears.
- **Unimodularity is a theorem, not an instance.** Mathlib has no `Unimodular` predicate;
  `IsHaarMeasure` extends *left* invariance only. Right-invariance of a particular
  group's Haar measure must be proved, and the port's
  `isMulRightInvariant_adelicGLHaar` (§3) is that proof for
  $`\mathrm{GL}_2(\mathbb{A}_F)`$.
- **Convolution is spelled directly.** Mathlib has measure convolution
  (`MeasureTheory.Measure.mconv`) and function convolution on normed spaces
  (`MeasureTheory.convolution`), but the port's `convKer`/`rc` write the integrals of §4
  by hand. This is what makes the Haar-invariance hypotheses visible in every statement.

## 8. Reading the two headlines with this in hand

The topic's §2.2–§2.5 become, in this order:

1. **Re-association (§4.3).** $`(\varphi \star f) \star h = \varphi \star (h \ast f)`$.
   Haar's left invariance makes the substitution $`x \mapsto yx`$ legal; compact support
   makes Fubini legal. No group-specific fact.
2. **The projected frame (§5).** A level-spherical $`f`$ is a cut; the measure $`\nu`$ is
   $`(\mu \restriction S) \circ \pi^{-1}`$, again Haar (open slab, compact level image),
   because a Haar measure on a product restricts to a product and pushes forward to a
   multiple of a Haar measure. The ambient problem becomes an archimedean one.
3. **The slices commute (§4.4).** On the archimedean group the kernel symmetry
   $`h \ast f = f \ast h`$ is proved by the multiplicity-one/type-span argument. Haar's
   contribution there is exactly the triplet "Haar, right-invariant, inversion-invariant"
   for $`\texttt{archNu}`$ — supplied by §5.2 from §3.
4. **The headline.** Substitute the kernel identity into the re-association.

The two variants of §2.5 do not change any of this: the compact file keeps the carrier
$`U`$ abstract and assumes `IsCompact U`/`IsOpen O`; the plain file takes
$`O = \texttt{levelOne}(N)`$, $`U = O \cap \mathrm{GL}_2(\widehat{\mathcal{O}}_F)`$ and
*proves* those side facts. In both cases the measure theory is the same.

The one Haar-theoretic theorem the two rows cite is
`NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar` (91 citers in the pin), and §3
is its content.

## 9. Where Haar measure is not the point

Haar measure makes the integrals define an associative, invariant convolution, and it
supplies the invariance that lets translations and inversions move through those
integrals. It does **not** give the commutation of the kernels. For the two particular
test functions, the equality $`h \ast f = f \ast h`$ is a statement that a certain
archimedean representation-theoretic object — the type algebra of the local
representations $`\tau_w`$ — acts centrally on the slice. That is the multiplicity-one
input of the topic's §2.4 (the `BiIsotypic` block: density of the algebra image in the
endomorphisms, contraction against the dual, the two-sided translate span, and the
pairing symmetry). It is representation theory, not measure theory, and this note does
not touch it. What the note supplies is the invariant integral on which that argument is
run.

## 10. The Lean map

### 10.1 The mathlib API

The general theory is spread over a handful of mathlib files, all at tag `v4.34.0`.

`Mathlib/MeasureTheory/Group/Defs.lean` defines the two invariance predicates:

```lean
class IsMulLeftInvariant [Mul G] (μ : Measure G) : Prop where
  map_mul_left_eq_self : ∀ g : G, map (g * ·) μ = μ

class IsMulRightInvariant [Mul G] (μ : Measure G) : Prop where
  map_mul_right_eq_self : ∀ g : G, map (· * g) μ = μ
```

([Defs.lean#L78-L92](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Group/Defs.lean#L78-L92).)

`Mathlib/MeasureTheory/Group/Measure.lean` defines the Haar predicate and the inversion
predicate, and gives the integral form of invariance in
`Mathlib/MeasureTheory/Group/Integral.lean`:

```lean
class IsHaarMeasure {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : Measure G) : Prop
  extends IsFiniteMeasureOnCompacts μ, IsMulLeftInvariant μ, IsOpenPosMeasure μ
```

([Measure.lean#L785-L787](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Group/Measure.lean#L785-L787));
`IsInvInvariant` is the class `μ.inv = μ`
([Measure.lean#L315-L318](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Group/Measure.lean#L315-L318)),
and the two lemmas the engine uses most are

```lean
theorem integral_mul_left_eq_self [IsMulLeftInvariant μ] (f : G → E) (g : G) :
    ∫ x, f (g * x) ∂μ = ∫ x, f x ∂μ
```

([Integral.lean#L92-L93](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Group/Integral.lean#L92-L93)) and its right-handed twin
([Integral.lean#L102](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Group/Integral.lean#L102)).

`Mathlib/MeasureTheory/Measure/Haar/Basic.lean` constructs the measure and normalizes it
by an arbitrary compact set:

```lean
noncomputable abbrev haar [LocallyCompactSpace G] : Measure G :=
  haarMeasure <| Classical.arbitrary _
```

([Basic.lean#L583-L584](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Measure/Haar/Basic.lean#L583-L584)); the instance
`isHaarMeasure_haarMeasure`
([Basic.lean#L574](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Measure/Haar/Basic.lean#L574)) is what the port's
definitions invoke. Uniqueness and the scaling constant are in
`Haar/Unique.lean`: `haarScalarFactor`
([Unique.lean#L278](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Measure/Haar/Unique.lean#L278)) and

```lean
lemma isMulLeftInvariant_eq_smul [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] :
    μ' = haarScalarFactor μ' μ • μ
```

([Unique.lean#L922-L925](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Measure/Haar/Unique.lean#L922-L925)). The modular character is
`MeasureTheory.Measure.modularCharacterFun`
([ModularCharacter.lean#L45](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Group/ModularCharacter.lean#L45)), with the defining property

```lean
lemma map_right_mul_eq_modularCharacterFun_smul [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsHaarMeasure μ] [InnerRegular μ] (g : G) : map (· * g) μ = modularCharacterFun g • μ
```

([ModularCharacter.lean#L93-L94](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Group/ModularCharacter.lean#L93-L94)).

### 10.2 The port's Haar layer

`NumberTheory/AdelicHaar/GeneralLinear.lean` is the measure the topic integrates against:
`glBorel` is `borel _` on $`\mathrm{GL}_2(\mathbb{A}_F)`$, and

```lean
def adelicGLHaar : @Measure (Matrix.GeneralLinearGroup n (AdeleRing R K)) (glBorel n R K) := by
  letI := glBorel n R K
  haveI := borelSpace_glBorel n R K
  exact Measure.haar
```

([GeneralLinear.lean#L60-L63](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/GeneralLinear.lean#L60-L63)), with `isHaarMeasure_adelicGLHaar` two lines below invoking
`Measure.isHaarMeasure_haarMeasure`. `Adele.lean` does the same additively:
`adelicAddHaar = Measure.addHaar`
([Adele.lean#L56-L59](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/Adele.lean#L56-L59)).

`NumberTheory/AdelicHaar/MulRightInvariant.lean` is §3. The headline is

```lean
theorem NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar (F : Type) [Field F] [NumberField F] :
    (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant
```

([MulRightInvariant.lean#L334-L335](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/MulRightInvariant.lean#L334-L335)). Its steps run in the order of §3:
the conjugation and square-root lemmas
([#L33-L55](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/MulRightInvariant.lean#L33-L55)); the reduction of right-invariance to
$`\Delta \equiv 1`$ via `haarScalarFactor`
([#L67-L77](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/MulRightInvariant.lean#L67-L77)); the matrix $`E, L, D, w, s`$
([#L87-L165](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/MulRightInvariant.lean#L87-L165)); the LDU decomposition and the
entry-unit reduction
([#L152-L202](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/MulRightInvariant.lean#L152-L202)); stable range at the finite places, the
infinite places, and the adeles
([#L212-L278](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/MulRightInvariant.lean#L212-L278),
[#L282-L299](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/MulRightInvariant.lean#L282-L299),
[#L303-L313](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/MulRightInvariant.lean#L303-L313)); and the final assembly
([#L321-L342](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/MulRightInvariant.lean#L321-L342)).

The generic convolution engine is `RepTheory/ProjectedHaar.lean`. The kernel is

```lean
def _root_.ProjectedHaar.convKer {H : Type*} [Group H] [MeasurableSpace H] (m : Measure H) (P Q : H → ℂ) (x : H) : ℂ :=
  ∫ y, P y * Q (y⁻¹ * x) ∂m
```

([ProjectedHaar.lean#L54-L55](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/RepTheory/ProjectedHaar.lean#L54-L55)); the frame and its algebra are §5.1
([#L43-L171](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/RepTheory/ProjectedHaar.lean#L43-L171)); $`\nu`$ is `nu`
([#L178](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/RepTheory/ProjectedHaar.lean#L178)); the three invariance lemmas of §5.2 are
`nu_isMulLeftInvariant`, `nu_isMulRightInvariant`, `nu_isOpenPosMeasure`
([#L211-L237](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/RepTheory/ProjectedHaar.lean#L211-L237),
[#L312-L323](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/RepTheory/ProjectedHaar.lean#L312-L323)), and they assemble into

```lean
theorem nu_isHaarMeasure [T2Space A] [μ.IsHaarMeasure] (hπ : Continuous Φ.π) (hι : Continuous Φ.ι)
    (hιf : Continuous Φ.ιf) (hUf : IsCompact (Uf : Set B)) (hS : IsOpen (slab Φ Uf)) : (nu Φ μ Uf).IsHaarMeasure
```

([ProjectedHaar.lean#L349-L353](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/RepTheory/ProjectedHaar.lean#L349-L353)). The engine `convKer_cut_comm`
([#L290-L297](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/RepTheory/ProjectedHaar.lean#L290-L297)) is §5.4; `rc` and `rc_rc`
([#L469-L470](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/RepTheory/ProjectedHaar.lean#L469-L470),
[#L520-L547](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/RepTheory/ProjectedHaar.lean#L520-L547)) are §4.3. The anti-involution machinery of §4.4 is
`RepTheory/AntiInvolutionHaar.lean`: `map_θ_eq_self`
([#L130-L161](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/RepTheory/AntiInvolutionHaar.lean#L130-L161)) is the $`c^2 = 1`$ argument,
`isInvInvariant` ([#L163-L166](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/RepTheory/AntiInvolutionHaar.lean#L163-L166)) is its $`\theta = \mathrm{inv}`$ case, and
`convKer_comm` ([#L223-L240](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/RepTheory/AntiInvolutionHaar.lean#L223-L240)) is the symmetry.

The adelic instantiation is `AutomorphicForm/Adelic/RightConvComm/`. The frame
`adelicFrame` is `Frame.lean:156–167`; `archNu` is

```lean
def archNu (U : Subgroup (AdelicGL2 (𝓞 F) F)) : Measure (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing F)) :=
  ProjectedHaar.nu (ProjectedHaar.adelicFrame F) (adelicGLHaar (Fin 2) (𝓞 F) F)
    (U.map (AdelicLevel.glFin (𝓞 F) F))
```

([MeasureAssembly.lean#L78-L80](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/AutomorphicForm/Adelic/RightConvComm/MeasureAssembly.lean#L78-L80)). The Haar/right/invariance facts are assembled at
[#L98-L121](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/AutomorphicForm/Adelic/RightConvComm/MeasureAssembly.lean#L98-L121), and `convKer_comm_of_types`
(`SliceCentrality.lean:93–104`) begins by installing exactly those three instances — the
three facts this note is about.

### 10.3 Encoding walls

Three Lean-specific points the topic file assumes.

1. **`IsHaarMeasure` means left-invariant.** A `[IsHaarMeasure μ]` instance gives
   `[IsMulLeftInvariant μ]` and nothing about the right. The topic needs
   `IsMulRightInvariant` of `adelicGLHaar` (through `archNu`) and obtains it only from
   `isMulRightInvariant_adelicGLHaar`. This is the single most important reading fact in
   the file.
2. **The Borel structure is an explicit argument.** `glBorel` is an `@[reducible] def`
   equal to `borel _`, not an instance, so the measure has type
   `@Measure G (glBorel …)`. Every definition and lemma restates
   `letI := glBorel …; haveI := borelSpace_glBorel …` around its body (the pin's
   `letI`/`haveI` walls; the port keeps them and disables the style linter for them).
   `MeasureAssembly.lean` installs the pair globally with
   `attribute [local instance] NumberField.AdelicHaar.glBorel archBorel` and the
   Haar/right-invariance facts as `private scoped instance`, and the engine opens them
   with `open scoped SecondCountableAdelic`.
3. **Restrict first, then push forward.** `nu` is `(μ.restrict slab).map π`, not
   `(μ.map π).restrict`. The restriction to the slab is what makes the pushforward a
   Haar measure; pushing forward the ambient $`\mu`$ would give a measure that is
   infinite (if $`U_f`$ is noncompact) or zero (if $`U_f`$ is a null set).

A fourth, minor point: `Measure.haar` (multiplicative) and `Measure.addHaar` (additive)
are the `to_additive` pair generated from one definition; the adele ring uses the second,
the general linear group the first.

### 10.4 Key-point table

| mathematics | Lean (mathlib at `v4.34.0`; port at `1995556`) | where |
|---|---|---|
| left/right invariance of a measure | `IsMulLeftInvariant`, `IsMulRightInvariant` | `Defs.lean:78,89` |
| Haar measure predicate | `IsHaarMeasure` = finite-on-compacts + left-invariant + open-positive | `Measure.lean:785` |
| existence, arbitrary normalization | `Measure.haar`, `Measure.addHaar` | `Haar/Basic.lean:583` |
| uniqueness and scaling constant | `haarMeasure_unique`, `haarScalarFactor`, `isMulLeftInvariant_eq_smul` | `Haar/Basic.lean:670`, `Haar/Unique.lean:278,922` |
| integral form of invariance | `integral_mul_left_eq_self`, `integral_mul_right_eq_self` | `Group/Integral.lean:92,102` |
| modular character $`\Delta_G`$ | `modularCharacterFun`, `modularCharacter`, `map_right_mul_eq_modularCharacterFun_smul` | `Group/ModularCharacter.lean:45,93` |
| inversion-invariance | `IsInvInvariant`, `Measure.inv` | `Measure.lean:304,315` |
| adelic multiplicative Haar | `adelicGLHaar`, `isHaarMeasure_adelicGLHaar` | `GeneralLinear.lean:60,65` |
| adelic additive Haar | `adelicAddHaar` | `Adele.lean:56` |
| $`\mathrm{GL}_2(\mathbb{A}_F)`$ unimodular | `isMulRightInvariant_adelicGLHaar` | `MulRightInvariant.lean:334` |
| stable range 1 (finite/infinite) | `unimodGL2_stable_{fin,inf,adele}` | `MulRightInvariant.lean:212,282,303` |
| convolution kernel | `ProjectedHaar.convKer` | `ProjectedHaar.lean:54` |
| right-regular pairing `rightConv` | `AutomorphicForm.rightConv`, `MeasureGlue.rc` | `RightConvolution.lean:23`, `Frame.lean:266` |
| associativity + Fubini | `KernelReduction.rc_rc`, `MeasureAssembly.rightConv_rightConv` | `ProjectedHaar.lean:520`, `MeasureAssembly.lean:126` |
| pushed-forward measure $`\nu`$ | `ProjectedHaar.nu` | `ProjectedHaar.lean:178` |
| $`\nu`$ is Haar | `ProjectedHaar.nu_isHaarMeasure` | `ProjectedHaar.lean:349` |
| $`\nu`$ right-invariant | `ProjectedHaar.nu_isMulRightInvariant` | `ProjectedHaar.lean:225` |
| inversion-invariance, generic and adelic | `AntiInvolutionHaar.isInvInvariant`, `MeasureAssembly.archNu_isInvInvariant` | `AntiInvolutionHaar.lean:163`, `MeasureAssembly.lean:109` |
| anti-involution invariance | `map_θ_eq_self`, `convKer_comm` | `AntiInvolutionHaar.lean:130,223` |
| adelic $`\nu`$ | `MeasureAssembly.archNu`, `archNu_isHaarMeasure` | `MeasureAssembly.lean:78,98` |
| projected engine | `ProjectedHaar.convKer_cut_comm` | `ProjectedHaar.lean:290` |
| projective quotient Haar | `adelicPGLHaar` | `AdelicCentre.lean:104` |

### 10.5 Links

Port (pinned at `1995556`):

- `NumberTheory/AdelicHaar/` —
  [Local](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/Local.lean),
  [Adele](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/Adele.lean),
  [GeneralLinear](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/GeneralLinear.lean),
  [MulRightInvariant](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicHaar/MulRightInvariant.lean);
- `RepTheory/`:
  [ProjectedHaar](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/RepTheory/ProjectedHaar.lean),
  [AntiInvolutionHaar](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/RepTheory/AntiInvolutionHaar.lean);
- `AutomorphicForm/Adelic/`:
  [RightConvolution](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/AutomorphicForm/Adelic/RightConvolution.lean),
  [RightConvComm/Frame](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/AutomorphicForm/Adelic/RightConvComm/Frame.lean),
  [RightConvComm/MeasureAssembly](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/AutomorphicForm/Adelic/RightConvComm/MeasureAssembly.lean),
  [RightConvComm/SliceCentrality](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/AutomorphicForm/Adelic/RightConvComm/SliceCentrality.lean);
- `NumberTheory/`:
  [AdelicCentre](https://github.com/htzh/flt_for_human/blob/1995556/lean/FLTForHuman/NumberTheory/AdelicCentre.lean).

Pin (pinned at `aa2d8b3`):

- definition node
  [`Definitions/Def_NumberField_AdelicHaar.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_NumberField_AdelicHaar.lean)
  (`adeleBorel` L132, `adelicAddHaar` L146, `glBorel` L176, `adelicGLHaar` L189,
  `isHaarMeasure_adelicGLHaar` L194);
- the unimodularity proof
  [`P2M/Sol/S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar.lean)
  (326 lines; `unimodGL2_ldu` L136, `unimodGL2_delta_of_stable` L181,
  `unimodGL2_stable_fin` L196, `unimodGL2_stable_inf` L266,
  `unimodGL2_stable_adele` L287);
- statement wrapper
  [`Theorems/Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar.lean).

Mathlib at `v4.34.0`:

- [`MeasureTheory/Group/Defs.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Group/Defs.lean),
  [`MeasureTheory/Group/Measure.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Group/Measure.lean),
  [`MeasureTheory/Group/Integral.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Group/Integral.lean),
  [`MeasureTheory/Group/Convolution.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Group/Convolution.lean),
  [`MeasureTheory/Group/ModularCharacter.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Group/ModularCharacter.lean);
- [`MeasureTheory/Measure/Haar/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Measure/Haar/Basic.lean),
  [`…/Haar/Unique.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Measure/Haar/Unique.lean),
  [`…/Haar/Quotient.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Measure/Haar/Quotient.lean).

Background: the topic file
[lean/topics/automorphicForm/TOPIC-rightConv-comm.md](../lean/topics/automorphicForm/TOPIC-rightConv-comm.md)
and its work order
[WORKORDER-P-rightConv-comm.md](../lean/topics/automorphicForm/WORKORDER-P-rightConv-comm.md);
the foundation effort [PORTING-AutomorphicForm.md](../lean/topics/PORTING-AutomorphicForm.md);
Halmos, *Measure Theory*, §53, and Gleason, *Existence and Uniqueness of Haar Measure*,
for the construction of §1.2.
