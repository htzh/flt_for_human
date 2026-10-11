# ℘-division values and the level-N modular curve

Twenty-sixth of the `math/` notes. [024](024-uniformization-versus-modular-functions.md)
contrasted the two ways the pin reaches the $`j`$-line: the modular-function field of
$`X_0(N)`$ built from $`q`$-expansions, and the analytic uniformization
$`\mathbb{C}/\Lambda \cong E(\mathbb{C})`$ built from the Weierstrass function $`\wp`$.
This note is about a third construction, which sits between the two: **the level-$`N`$
modular curve built from the values of $`\wp`$ at $`N`$-division points.**

The uniformization identifies not only the curve with the torus, but the whole torsion
subgroup,

$$E[N] \\;\cong\\; \tfrac{1}{N}\Lambda/\Lambda \\;\cong\\; (\mathbb{Z}/N)^2,$$

and the image of the point $`z_v = (v_0\tau+v_1)/N`$ has affine coordinates
$`(\wp(z_v), \wp'(z_v)/2)`$. So $`\wp`$ at torsion points *is* a coordinate system on the
level-$`N`$ structure, and the functions $`\tau \mapsto \wp_{(\tau,1)}(z_v)`$ generate the
function field of $`X(N)`$. This is the classical theory of **Fricke functions**.

The short version, before the machinery:

- $`\wp`$ at torsion is not a modular function: as a function of $`\tau`$ it transforms
  with weight $`2`$. The **Fricke function** $`f_v`$ is the weight-zero correction,
  obtained by multiplying by the weight-$`(-2)`$ form $`E_4E_6/\Delta`$. These $`f_v`$
  are the modular functions of level $`N`$.
- $`\mathrm{SL}_2(\mathbb{Z})`$ permutes them, $`f_a(\gamma\tau) = f_{a\gamma}(\tau)`$,
  where $`\gamma`$ acts on $`a \in (\mathbb{Z}/N)^2`$ by right multiplication. The tuple
  $`(f_v)_{v \neq 0}`$ is fixed exactly by $`\pm\Gamma(N)`$. That is the level structure.
- $`\mathbb{C}(X(N)) = \mathbb{C}(j, f_v : v \neq 0)`$ is Galois over $`\mathbb{C}(j)`$
  with group $`\mathrm{SL}_2(\mathbb{Z})/\pm\Gamma(N)`$, of degree equal to the index.
- The arithmetic of the level structure is Shimura's reciprocity law: the cyclotomic
  Galois group acts on the $`q`$-expansions of the $`\Delta f_v`$ by the diamond action.

The Lean encoding is compressed into §8; the mathematics is §1–§7.

## 1. The lattice model

Fix $`\tau`$ in the upper half-plane $`\mathbb{H}`$ and the lattice
$`\Lambda_\tau = \mathbb{Z}\tau + \mathbb{Z}`$. The Weierstrass function and its
derivative are

$$\wp(z) = \frac{1}{z^2} + \sum_{l \in \Lambda_\tau \setminus \\{0\\}}
  \left(\frac{1}{(z-l)^2} - \frac{1}{l^2}\right), \qquad
  \wp'(z) = -2\sum_{l \in \Lambda_\tau}\frac{1}{(z-l)^3},$$

and they satisfy the differential equation $`\wp'^2 = 4\wp^3 - g_2\wp - g_3`$ with

$$g_2 = 60\sum_{l \neq 0}\frac{1}{l^4}, \qquad
  g_3 = 140\sum_{l \neq 0}\frac{1}{l^6}.$$

The map

$$\mathbb{C}/\Lambda_\tau \longrightarrow E_\tau(\mathbb{C}), \qquad
  z \longmapsto (\wp(z),\\, \wp'(z)/2), \qquad
  E_\tau : y^2 = 4x^3 - g_2(\tau)x - g_3(\tau),$$

is an isomorphism of groups — this is the uniformization theorem of
[024 §3](024-uniformization-versus-modular-functions.md#3-theory-p-uniformization), proved
from $`\wp`$ alone. The lattice points are exactly the poles, and they map to the origin.

The connection with the modular forms of level one is through the classical identities

$$g_2 = \frac{(2\pi)^4}{12}\\,E_4, \qquad
  g_3 = \frac{(2\pi)^6}{216}\\,E_6, \qquad
  \Delta = \frac{E_4^3 - E_6^2}{1728} = q\prod_{n\ge1}(1-q^n)^{24},$$

so that the modular invariant is $`j = 1728\,g_2^3/(g_2^3 - 27g_3^2) = E_4^3/\Delta`$.
We write $`q = e^{2\pi i\tau}`$ and $`\Delta(\tau)`$ for the normalised cusp form
$`(E_4^3-E_6^2)/1728`$, the same normalisation the pin's `jAnalytic` and
`ModularForm.discriminant` use.

## 2. Division points and their ℘-coordinates

The $`N`$-torsion of $`\mathbb{C}/\Lambda_\tau`$ is

$$\tfrac{1}{N}\Lambda_\tau/\Lambda_\tau
  = \left\\{\tfrac{v_0\tau+v_1}{N} : v_0, v_1 \in \mathbb{Z}/N\mathbb{Z}\right\\}
  \cong (\mathbb{Z}/N)^2,$$

with the standard generators $`\tau/N`$ and $`1/N`$. Indexing by
$`v = (v_0,v_1) \in (\mathbb{Z}/N)^2`$, write

$$z_v = \frac{\tilde v_0\tau + \tilde v_1}{N},$$

where $`\tilde v_i`$ is the representative of $`v_i`$ in $`\{0,\dots,N-1\}`$. The Weil
pairing is the standard symplectic form,

$$e_N(z_v, z_w) = \exp\left(\frac{2\pi i (v_0w_1 - v_1w_0)}{N}\right),$$

so that a *full level-$`N`$ structure* is a pair $`(P,Q)`$ of $`N`$-torsion points that is
a $`\mathbb{Z}/N`$-basis with $`e_N(P,Q) = e^{2\pi i/N}`$; in the model above it is the
pair $`(\tau/N,\,1/N)`$.

The coordinates of the point $`z_v`$ on $`E_\tau`$ are $`(\wp(z_v),\wp'(z_v)/2)`$. The
$`x`$-coordinate is the one that carries the level structure, and it is convenient to
normalise it by

$$W_v(\tau) = (2\pi i)^{-2}\\,\wp_{(\tau,1)}(z_v).$$

The factor $`(2\pi i)^{-2}`$ is the normalisation that makes $`W_v`$ a **weight-two form
with cyclotomic coefficients**: under a change of lattice $`\wp`$ scales with weight
$`2`$, and the factor removes the transcendental constant so that the $`q`$-expansion
coefficients are cyclotomic.

Two facts about the $`W_v`$ drive everything below.

**(a) The slash action.** For $`\gamma \in \mathrm{SL}_2(\mathbb{Z})`$, acting on
$`(\mathbb{Z}/N)^2`$ by right multiplication of the row vector,

$$W_a \mid_2 \gamma = W_{a\bar\gamma}, \qquad
  (a\bar\gamma)_j = \sum_i a_i\\,\bar\gamma_{ij} \bmod N,$$

where $`\bar\gamma`$ is $`\gamma`$ reduced modulo $`N`$. In particular $`W_a`$ is a
weight-two modular form for $`\Gamma(N)`$, and the slash action permutes the $`W_a`$
through the finite group $`\mathrm{SL}_2(\mathbb{Z}/N)`$.

**(b) The $`q`$-expansion (Lipschitz).** With $`u = u_{a}(\tau) = e^{2\pi i z_a} =
\zeta_N^{a_1} q^{a_0/N}`$ and $`\zeta_N = e^{2\pi i/N}`$,

$$W_a(\tau) = \frac{u}{(1-u)^2} + \frac{1}{12} +
  \sum_{p_0 \ge 1}\sum_{p_1 \ge 1} p_1\\,(u^{p_1} + u^{-p_1} - 2)\\,q^{p_0 p_1}.$$

This is a power series in $`q^{1/N}`$ whose coefficients lie in $`\mathbb{Z}[\zeta_N]`$.
At the cusp $`q \to 0`$ it specialises to

$$W_a(i\infty) = \frac{\zeta_N^{a_1}}{(1-\zeta_N^{a_1})^2} + \frac{1}{12}
  = -\frac{1}{4\sin^2(\pi a_1/N)} + \frac{1}{12}
  \quad \text{if } a_0 = 0, \qquad W_a(i\infty) = \frac{1}{12} \quad \text{otherwise,}$$

so that the raw $`\wp`$-value tends to $`\pi^2/\sin^2(\pi a_1/N) - \pi^2/3`$ in the first
case and to $`-\pi^2/3`$ in the second.

The weight-two form $`W_a`$ is not a modular function: it is not $`\Gamma(N)`$-invariant,
it is merely a form. To descend to functions one must divide by a weight-$`(-2)`$ form,
and the classical choice is $`E_4E_6/\Delta`$.

## 3. The Fricke functions

Define

$$f_v(\tau) = -\frac{1}{2592}\\,\frac{E_4(\tau)E_6(\tau)}{\Delta(\tau)}\\,W_v(\tau).$$

The factor $`E_4E_6/\Delta`$ is holomorphic on $`\mathbb{H}`$ — its only poles are at the
cusps, where $`\Delta`$ vanishes — and it has weight $`-2`$, so the product with the
weight-two form $`W_v`$ has weight zero. Since $`g_2g_3/\Delta`$ is a nonzero constant
multiple of $`E_4E_6/\Delta`$ (by the identities of §1), the pin's $`f_v`$ agrees, up to a
nonzero constant, with the classical normalisation $`(g_2g_3/\Delta)\cdot\wp(z_v)`$. The
constant is irrelevant to everything below: it does not change the field generated, the
transformation law, or the invariance.

The properties that make $`f_v`$ the level-$`N`$ coordinates are:

1. **Transformation.** $`f_a(\gamma\tau) = f_{a\bar\gamma}(\tau)`$ for all
   $`\gamma \in \mathrm{SL}_2(\mathbb{Z})`$. Hence the tuple $`(f_v)_{v \neq 0}`$ carries a
   permutation action of $`\mathrm{SL}_2(\mathbb{Z})`$ through $`\mathrm{SL}_2(\mathbb{Z}/N)`$.
2. **Level.** $`f_a`$ is invariant under $`\Gamma(N)`$, and the *stabiliser of the whole
   tuple* is exactly $`\pm\Gamma(N)`$:
   $$\{\gamma : f_{a\bar\gamma} = f_a \text{ for all } a \neq 0\} = \{\gamma : \gamma \in \Gamma(N) \text{ or } -\gamma \in \Gamma(N)\}.$$
   This is the precise sense in which the collection $`(f_v)_{v\neq0}`$ *is* the full
   level-$`N`$ structure: a transformation preserving every Fricke coordinate is
   $`\pm`$ a principal-congruence element.
3. **Evenness and injectivity.** $`f_{-v} = f_v`$, and for $`a,b \neq 0`$,
   $`f_a = f_b`$ if and only if $`b = \pm a`$. For $`N \ge 3`$ this pairs the $`N^2-1`$
   functions into $`(N^2-1)/2`$ classes, matching the nonzero torsion points modulo sign;
   at $`N = 2`$ the relation $`v = -v`$ is vacuous and the three functions are distinct.
4. **Holomorphy and growth.** Each $`f_v`$ with $`v \neq 0`$ is holomorphic on
   $`\mathbb{H}`$, and $`f_v\,\Delta`$ is bounded at $`i\infty`$. The order-one pole of
   $`f_v`$ at the cusp is exactly compensated by the zero of $`\Delta`$.
5. **Rationality.** The width-$`N`$ $`q`$-expansion of $`f_v\,\Delta`$ has coefficients in
   the cyclotomic field $`\mathbb{Q}(\zeta_N)`$.
6. **Integrality over $`\mathbb{C}[j]`$.** For each $`v \neq 0`$ there is a monic
   polynomial relation of degree $`N^2-1`$,
   $$f_v^{N^2-1} + \sum_{k \lt N^2-1} P_k(j)\,f_v^k = 0, \qquad P_k \in \mathbb{C}[X],$$
   with cyclotomic coefficients. Equivalently, $`f_v`$ is integral over $`\mathbb{C}[j]`$,
   and the full orbit polynomial $`\prod_{v\neq0}(X - f_v)`$ has $`\mathbb{C}[j]`$-coefficients.

Properties 1–3 are the level structure; 4–6 are what make it usable arithmetically. The
last point is the level-$`N`$ analogue of the level-one integrality of $`j`$: it is why
bounded-denominator arguments can be run at level $`N`$ with the Fricke coordinates
exactly as they are run at level one with $`j`$.

## 4. The level-N curve X(N)

Let $`\Gamma(N) = \{\gamma \in \mathrm{SL}_2(\mathbb{Z}) : \gamma \equiv I \bmod N\}`$ be
the principal congruence subgroup, and put

$$Y(N) = \Gamma(N)\backslash\mathbb{H}, \qquad
  X(N) = Y(N) \cup \\{\text{cusps}\\} = \Gamma(N)\backslash(\mathbb{H} \cup \mathbb{P}^1(\mathbb{Q})).$$

The classical moduli interpretation is

$$Y(N)(\mathbb{C}) \\;\longleftrightarrow\\;
  \\{(E, P, Q) : E/\mathbb{C} \text{ elliptic},\ (P,Q) \text{ a } \mathbb{Z}/N\text{-basis of } E[N],\ e_N(P,Q) = \zeta_N\\},$$

the map being $`\tau \mapsto (\mathbb{C}/\Lambda_\tau,\, \tau/N,\, 1/N)`$. Injectivity
modulo $`\Gamma(N)`$ is the statement that the pair $`(E, P, Q)`$ determines the lattice
up to a basis change in $`\Gamma(N)`$; surjectivity is the uniformization theorem applied
to a basis of the torsion and a choice of basis of the lattice.

Two constructions of the function field $`\mathbb{C}(X(N))`$ follow.

- **Analytically**, from the $`\wp`$-coordinates: the Fricke functions of §3 are modular
  functions of level $`N`$, holomorphic on $`\mathbb{H}`$ and meromorphic at the cusps,
  so they lie in $`\mathbb{C}(X(N))`$. They separate the $`N`$-torsion, and together with
  $`j`$ they generate. Write
  $$A_N = \mathbb{C}[j, f_v : v \neq 0] \subseteq \mathbb{C}(X(N)).$$
- **Moduli-theoretically**, the level structure is the data $`(E,P,Q)`$; the field of
  modular functions of level $`N`$ is by definition the field of functions on the moduli
  problem.

The two agree: $`\mathbb{C}(X(N))`$ is the fraction field of $`A_N`$, and $`A_N`$ consists
of functions holomorphic on $`\mathbb{H}`$ (with poles only at the cusps). The
generation statement in this form is classical: **every modular function of level $`N`$
is a rational function of $`j`$ and the Fricke functions**, i.e. it can be written
$`F = a/b`$ with $`a,b \in A_N`$ and $`b \neq 0`$ as a function. This is the level-$`N`$
companion of $`\mathbb{C}(X(1)) = \mathbb{C}(j)`$ and of the level-$`N`$ generation theorem
of [010](010-function-field-generation.md); the difference is that here the generators are
the ℘-division values rather than $`q`$-expansion data.

The Galois theory of the cover is the classical description of $`X(N)`$:

$$\mathrm{Gal}\bigl(\mathbb{C}(X(N))/\mathbb{C}(j)\bigr)
  \\;\cong\\; \mathrm{SL}_2(\mathbb{Z})/\pm\Gamma(N),$$

acting on functions by $`F \mapsto F \circ \gamma^{-1}`$; the fixed field is
$`\mathbb{C}(j)`$, the degree is the index
$`[\mathrm{SL}_2(\mathbb{Z}) : \pm\Gamma(N)]`$, and the extension is Galois. For
$`N \ge 3`$ the group is $`\mathrm{PSL}_2(\mathbb{Z}/N)`$, since $`-I`$ is not congruent
to $`I`$ modulo $`N`$; for $`N = 1,2`$ the $`\pm`$ already lies in $`\Gamma(N)`$ and the
group is $`\mathrm{SL}_2(\mathbb{Z}/N)`$ (of order $`6`$ at $`N = 2`$). The pin states the
theorem uniformly with the $`\pm`$, which is exactly what handles the small levels.

Three features are worth isolating.

- The cover $`X(N) \to X(1)`$ is *not* the cover $`X_0(N) \to X(1)`$ of
  [010](010-function-field-generation.md): the latter is a moduli problem of cyclic
  subgroups (a $`\Gamma_0`$-type level), the former one of full bases with the pairing
  fixed. The two towers meet in the proof (through the Hecke/Jacobian layer), but they are
  different moduli problems and different function fields.
- The group law only enters through $`\wp`$: the coordinates on $`E[N]`$ are
  $`(\wp, \wp'/2)`$, and the Fricke functions are $`\wp`$ alone. The $`y`$-coordinate
  $`\wp'`$ is not needed for the level structure over $`\mathbb{C}`$; it is determined by
  the $`x`$-coordinate up to sign, and the sign ambiguity is precisely the $`f_v = f_{-v}`$
  of §3.
- The description is a *function-field* description of $`X(N)`$, not a moduli functor:
  $`A_N`$ is a ring of meromorphic functions on $`\mathbb{H}`$, not a representable
  functor. Whether the pin could have built the ℘-level-$`N`$ curve as a moduli problem
  instead is taken up in §7.

## 5. Arithmetic: q-expansions and Shimura reciprocity

The reason the Fricke coordinates are the *arithmetic* coordinates, and not merely a
convenient analytic presentation, is that the Galois action on their $`q`$-expansions is
explicit.

Let $`s`$ be coprime to $`N`$ and let $`\varphi : \mathbb{Q}(\zeta_N) \to \mathbb{C}`$ be a
ring homomorphism sending $`\zeta_N`$ to $`\zeta_N^s`$. Then the coefficients of the
width-$`N`$ $`q`$-expansion transform by the **diamond action**:

$$\varphi\bigl(\text{coeff of } q^n \text{ in } \Delta f_{(a_0,a_1)}\bigr)
  = \text{coeff of } q^n \text{ in } \Delta f_{(a_0,\\,s a_1)}.$$

In words: the cyclotomic Galois group $`(\mathbb{Z}/N)^\times`$ acts on the level-$`N`$
structure by scaling the second coordinate of the torsion index. This is the reciprocity
law for the modular function field, and it is what makes the level-$`N`$ structure
arithmetic: the Fricke coordinates are defined over the cyclotomic field
$`\mathbb{Q}(\zeta_N)`$, and the diamond action
$`(\mathbb{Z}/N)^\times = \mathrm{Gal}(\mathbb{Q}(\zeta_N)/\mathbb{Q})`$ is the Galois
action on that field of definition.

The general form of the statement, which is what the pin's proof consumes, is the
reciprocity law *at the cusps*. For a holomorphic, $`\Gamma_1(N)`$-invariant, pole-bounded
function $`G`$ with rational $`q`$-expansion, and an embedding
$`\iota : \overline{\mathbb{Q}} \hookrightarrow \mathbb{C}`$, there are algebraic numbers
$`a_n`$ with

$$\bigl(q\text{-expansion of } (G \circ S)\cdot\Delta^m \text{ at width } N\bigr)_n = \iota(a_n),$$

and for every $`\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})`$ with
$`\sigma(\zeta) = \zeta^c`$ and every
$`\gamma \in \mathrm{SL}_2(\mathbb{Z})`$ with $`\gamma_{01} \equiv 0`$ and
$`\gamma_{11} \equiv c \pmod N`$, the $`n`$-th coefficient of the corresponding translate
is $`\iota(\sigma(a_n))`$. The Fricke-function statement above is the special case in
which $`G`$ is a $`\Delta`$-multiple of $`f_v`$.

Two consequences are used downstream:

- **Galois-stable integral structure.** Because the coefficients lie in
  $`\mathbb{Q}(\zeta_N)`$ and the action is the diamond action, the space of
  $`\mathbb{Q}`$-rational (or $`K`$-rational) cusp forms is stable under the Galois action
  transported to the coefficient field. This is the level-$`N`$ input to the integral
  basis of $`\Gamma_1(N)`$ cusp forms in [013](013-integral-structure-gamma1-basis.md).
- **Spanning by Eisenstein-type forms.** The pin's spanning theorem
  (`CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top`) says that for every congruence
  subgroup $`\Gamma \supseteq \Gamma(N)`$ and every tuple of weights with
  $`k + 4a + 6b = 12m`$, the weight-$`k`$ cusp forms $`f`$ on $`\Gamma`$ for which
  $`f\,E_4^aE_6^b\,Q`$ is a $`\Delta^m`$-multiple of a Fricke-polynomial $`P`$ span the
  whole space of weight-$`k`$ cusp forms on $`\Gamma`$. The polynomial generators are
  $`j`$ and the $`f_v`$, i.e. exactly the ring $`A_N`$; this is the level-$`N`$ version of
  the classical fact that $`E_4, E_6`$ generate the ring of modular forms.

## 6. The Γ₁(N) specialisation

There is a one-parameter version of the same construction, which is the one that looks
most like a classical Eisenstein series. Instead of the full tuple $`\{f_v\}`$, take the
divisions $`\wp(t/M)`$ for $`t \in \mathbb{Z}/M`$ alone. The corresponding normalised
functions

$$W_t(\tau) = 12\\,(2\pi i)^{-2}\\,\wp_{(\tau,1)}(t/M)$$

are modular forms of weight $`2`$ for $`\Gamma_1(M)`$, and their slash action with respect
to $`\Gamma_0(M)`$ is by the diamond character,
$`W_t \mid_2 \gamma = W_{t\cdot\gamma_{11}}`$. Their $`q`$-expansions are completely
explicit:

$$[q^n]\\,W_t = 12\left(\sum_{d \mid n} d\left(\zeta_M^{td} + \zeta_M^{-td}\right) -
  2\sum_{d\mid n} d\right) \quad (n \ge 1), \qquad
  [q^0]\\,W_t = 1 + 12\\,\frac{\zeta_M^{t}}{(1-\zeta_M^{t})^2},$$

with $`\zeta_M = e^{2\pi i/M}`$. These are the weight-two level-$`\Gamma_1`$ Eisenstein
series realised as division values; their non-modular corrections cancel, which is why
they are genuine forms. The same statement with $`(2\pi i)^{-2}`$ replaced by the
normalisation of §3 recovers the Fricke functions.

Why the proof wants both forms: the full tuple $`\{f_v\}`$ gives the Galois-theoretic level
structure and the function field of $`X(N)`$; the one-parameter family $`\{W_t\}`$ gives
the explicit integral $`q`$-expansions and the diamond character on $`\Gamma_1`$. The two
are tied together by the identity

$$f_v = -\frac{1}{2592}\\,\frac{E_4E_6}{\Delta}\cdot W_v,$$

i.e. the Fricke functions are the weight-zero shadows of the weight-two division-value
forms.

## 7. Why not "just Λ"

This is the point of the present note, so it is worth stating sharply. In the
uniformization slice of [024](024-uniformization-versus-modular-functions.md) one can
work with the abstract lattice $`\Lambda`$: the isogeny/sublattice dictionary, the
classification of complex elliptic curves, and the analytic lift are all statements about
$`\mathbb{C}/\Lambda`$ and its finite subgroups. Nothing there needs the individual
torsion *coordinates*.

The level-$`N`$ theory is different, and not derivable from $`\Lambda`$ alone in the
formalisation:

- $`\Lambda`$ gives the abstract torsion subgroup $`\frac{1}{N}\Lambda/\Lambda`$ and its
  points; it does not give a *function* on $`\mathbb{H}`$ or a $`q`$-expansion. The Fricke
  functions are those functions, and they are the objects the arithmetic statements in
  §5 are about.
- The level structure is the *orbit of the tuple of ℘-coordinates* under
  $`\mathrm{SL}_2(\mathbb{Z})`$; the stabiliser computation (property 2 of §3) is a
  statement about those functions, not about the abstract group $`E[N]`$.
- Conversely, the Fricke functions alone do not give the moduli interpretation: to say
  that $`Y(N)`$ parametrises pairs $`(E,P,Q)`$ one needs the uniformization, i.e. $`\Lambda`$.
  The two descriptions meet exactly at the point where a lattice model of the pair is
  needed.

So the honest summary is that both $`\Lambda`$ and the ℘-division values are used, for
different things: $`\Lambda`$ for the moduli interpretation and the isogeny dictionary,
the ℘-division values for the modular function field and its arithmetic. The level-$`N`$
construction is not an implicit use of $`\Lambda`$; it is the explicit construction of the
Fricke coordinates on top of it.

A caveat on the shape of what exists. The pin carries the level-$`N`$ construction as a
*function-field* development, not as a synthetic full-level moduli functor over
$`\mathbb{C}`$: there is no structure in the style of the $`\Gamma_0`$-pair moduli problem
[`Def_ModularCurve_ModuliPoint.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ModuliPoint.lean)
whose points carry the Fricke coordinates. The analytic level structure lives in the
algebra $`A_N = \mathbb{C}[j, f_v]`$ and in the Galois action on its $`q`$-expansions. The
pin's `FullLevel` structures — for instance
[`CerednikDrinfeld.QMFineModuli.FullLevel`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CerednikDrinfeld_QMFineModuli.lean)
and the `FullLevelTate.*` family — belong to the $`p`$-adic fake-elliptic-curve/Tate
setting, not to the ℘-level-`N` curve.

## 8. Lean technicalities

The rest of the note is a map of the formalisation. The mathematical content is the
preceding sections; this one records names, statement shapes and where the objects live.
All line numbers are for the pinned commit `aa2d8b3`; mathlib citations are at tag
`v4.34.0`.

**The definitions.** The canonical objects live in
[`Definitions/Def_ModularCurve_LevelNFunctionField.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_LevelNFunctionField.lean),
inside the namespace `ModularCurve.LevelN`:

| Lean | line | mathematics |
|---|---|---|
| `wp (N) (v) (τ)` | 14 | $`(2\pi i)^{-2}\wp_{(\tau,1)}(z_v)`$ |
| `fricke (N) (v) (τ)` | 19 | $`-\frac{1}{2592}\frac{E_4E_6}{\Delta}\,W_v`$ |
| `jAnalytic (τ)` | 22 | $`E_4^3/\Delta`$ |
| `generators (N)` | 25 | $`\{j\} \cup \{f_v : v \neq 0\}`$ |
| `ring (N)` | 28 | $`A_N = \mathbb{C}[j, f_v : v\neq0]`$ |
| `jGen (N)` | 44 | $`j`$ as an element of $`A_N`$ |

`wp` uses `PeriodPair.ofTau τ`, mathlib's `PeriodPair` with periods $`\omega_1 = \tau`$,
$`\omega_2 = 1`$ (its `indep` field is
`linearIndependent_coe_upperHalfPlane_one`, from $`\tau.\mathrm{im} \gt 0`$). So the
formalisation fixes the lattice model once, whereas the package theorems below are
stated for a general normalised family $`L : \mathbb{H} \to \mathrm{PeriodPair}`$.

**The package theorems.** The mathematics of §2, §3 and §5 is formalised as the following
"packages", each a single conjunction of the statements it names. They take $`L`$ with
the normalisation hypothesis $`hL : \forall \tau, (L\tau).\omega_1 = \tau \wedge
(L\tau).\omega_2 = 1`$, and they take $`W`$, `fricke`, `jf` together with *hypotheses*
pinning them to their formulas (`hW`, `hfricke`, `hjf`) rather than using the definitions
directly. That is a porting artifact of the `WLight` layer: the same statement is
instantiated at `LevelN.wp`, `LevelN.fricke`, `LevelN.jAnalytic` when the canonical
objects are wanted. A second artifact is that the `WLight` files import
`Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass` but not the pin's level-N
definition module, so the equations are hypotheses rather than `rfl`.

| theorem | file (line) | content |
|---|---|---|
| `PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty` | [Thm, 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty.lean#L9) | $`W_a`$ is a weight-2 form on $`\Gamma(N)`$; $`W_a\mid_2\gamma = W_{a\bar\gamma}`$; cusp value |
| `WLight.weierstrassP_qExpansion_package` | [Thm, 11](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WLight_weierstrassP_qExpansion_package.lean#L11) | the Lipschitz expansion of §2, and the scaling law $`\wp_{c\Lambda}(cz) = c^{-2}\wp_\Lambda(z)`$ |
| `WLight.frickeFunction_modularity_package` | [Thm, 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WLight_frickeFunction_modularity_package.lean#L16) | §3 properties 1–5: equivariance, evenness, holomorphy, boundedness, $`\mathbb{Q}(\zeta_N)`$ coefficients, injectivity, $`\Gamma(N)`$-invariance, reciprocity |
| `WLight.frickeFunction_orbit_package` | [Thm, 15](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WLight_frickeFunction_orbit_package.lean#L15) | §3 property 6: monic relation of degree $`N^2-1`$ over $`\mathbb{C}[j]`$, cyclotomic coefficients |
| `WLight.levelN_structure_package` | [Thm, 12](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WLight_levelN_structure_package.lean#L12) | §3 property 2 (stabiliser $`=\pm\Gamma(N)`$) plus the algebra structure of $`A_N`$: fractions, integrality, no zero divisors |
| `WLight.exists_levelFraction_of_stable_family` | [Thm, 12](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WLight_exists_levelFraction_of_stable_family.lean#L12) | §4 generation: every level-$`N`$ function in a $`\mathrm{SL}_2(\mathbb{Z})`$-stable family is $`F = a/b`$, $`a,b \in A_N`$ |
| `ModularForm.weierstrassP_torsion_qExpansion_package` | [Thm, 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_weierstrassP_torsion_qExpansion_package.lean#L13) | §2 regularity and rationality in the $`(a_0,a_1)`$-indexing, plus the diamond transport |
| `PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff` | [Thm, 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff.lean#L9) | §6: the weight-2 $`\Gamma_1(M)`$ forms $`12(2\pi i)^{-2}\wp(t/M)`$ and their explicit coefficients |
| `ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin` | [Thm, 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin.lean#L10) | §4: $`\mathbb{C}(X(N))/\mathbb{C}(j)`$ is Galois with group $`\mathrm{SL}_2(\mathbb{Z})/\pm\Gamma(N)`$, degree the index, fixed field $`\mathbb{C}(j)`$ |
| `ModularCurve.exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion` | [Thm, 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion.lean#L7) | §5 reciprocity at the cusps for general $`\Gamma_1(N)`$-invariant $`G`$ |

**Statement shapes worth knowing.**

- The Galois theorem is stated with an *arbitrary* field $`K`$ carrying compatible
  $`\mathbb{C}`$- and $`A_N`$-algebra structures and a `IsFractionRing (ring N) K`. It
  then produces the stability `hst` of `ring N` under $`F \mapsto F \circ \gamma`$, the
  monoid homomorphism $`\sigma : \mathrm{SL}_2(\mathbb{Z}) \to (K \simeq_\mathbb{C} K)`$,
  the kernel $`\Gamma(N) \sqcup \langle -1\rangle`$, the fixed field
  $`\mathrm{IntermediateField.adjoin}\,\mathbb{C}\,\{j\}`$, the transcendence of $`j`$,
  and the finite-dimensionality and Galois-ness with the index as degree. This is the
  function-field form of the moduli statement; it does not construct a curve.
- The cusp-value theorem `…tendsto_atImInfty` is stated for **raw** $`\wp`$, not for the
  normalised $`W_v`$; its limit is $`\pi^2/\sin^2(\pi a_1/N) - \pi^2/3`$, which is
  $`(2\pi i)^2`$ times the $`W_v`$ limit of §2. The normalisation convention therefore
  differs between files, and the reader should check which one a given statement uses.
- The $`q`$-expansion used in §5 is mathlib's `UpperHalfPlane.qExpansion h f` at period
  `h = N` (`qExpansion N`), whose coefficients are the Taylor coefficients of the
  `cuspFunction` at $`q = 0`$. There is no separate width-$`N`$ notion in the pin; the
  period is the mathlib argument.

**What mathlib supplies and what the pin builds.** mathlib has $`\wp`$ and its analytic
theory: `PeriodPair` (structure at
[Weierstrass.lean, 60](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean#L60)),
`weierstrassP` ([268](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean#L268)),
`derivWeierstrassP_sq`
([1075](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean#L1075)),
the pole order, periodicity and evenness; and it has the modular-forms vocabulary
$`E_4`$, $`E_6`$, `discriminant`, `qExpansion`, `congruence subgroups`
([`Gamma` 41](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L41)).
It has **no** Fricke-function theory, no level-$`N`$ function field, and no
$`\wp`$-division-value or Fricke reciprocity statement. All of §2–§6 above is the pin's,
built on those two mathlib layers.

**Why it reaches the root.** The layer is not decorative. The shortest citation path from
`WLight.levelN_structure_package` to `FLT.fermatLastTheorem` runs

`WLight.levelN_structure_package` $`\to`$
`ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0` $`\to`$
`ModularCurve.heckeDiamondInputsHAll` $`\to`$
`WeierstrassCurve.exists_hasLowerLevelTorsion_jZero_of_twoNewEigenformCongruence_sqf_five`
$`\to`$ … $`\to`$
`FreyPackage.level_lowering_to_two` $`\to`$
`FreyPackage.no_frey_package` $`\to`$
`FLT.fermatLastTheorem`,

i.e. the Fricke/level-$`N`$ layer feeds the diamond/Hecke input to the level-lowering
argument. The package is cited by roughly thirty theorems; the most structural consumers
are `CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top` (the spanning of §5) and
`ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin` (the Galois structure
of §4).

**Relation to [024](024-uniformization-versus-modular-functions.md).** That note separated
the "modular functions" route (its theory J) from the "uniformization" route (its theory
P) and observed that theory J contains no $`\wp`$. The present note shows that the two
axes are independent: the level-$`N`$ curve is built *from* $`\wp`$-division values, yet
it is a modular-function statement, with a $`q`$-expansion and a Galois action. The
separation in 024 is about the level-one and $`X_0(N)`$ generation slice, not about the
level-$`N`$ slice.

## Links

Pinned pin sources (`aa2d8b3`):

- [`Definitions/Def_ModularCurve_LevelNFunctionField.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_LevelNFunctionField.lean) — `wp` (14), `fricke` (19), `jAnalytic` (22), `generators` (25), `ring` (28), `jGen` (44)
- [`Theorems/Thm_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty.lean#L9) — slash action and cusp value
- [`Theorems/Thm_WLight_weierstrassP_qExpansion_package.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WLight_weierstrassP_qExpansion_package.lean#L11) — Lipschitz
- [`Theorems/Thm_WLight_frickeFunction_modularity_package.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WLight_frickeFunction_modularity_package.lean#L16) — transformation, rationality, reciprocity
- [`Theorems/Thm_WLight_frickeFunction_orbit_package.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WLight_frickeFunction_orbit_package.lean#L15) — the monic relation
- [`Theorems/Thm_WLight_levelN_structure_package.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WLight_levelN_structure_package.lean#L12) — stabiliser and algebra structure
- [`Theorems/Thm_WLight_exists_levelFraction_of_stable_family.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WLight_exists_levelFraction_of_stable_family.lean#L12) — generation as fractions
- [`Theorems/Thm_ModularForm_weierstrassP_torsion_qExpansion_package.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_weierstrassP_torsion_qExpansion_package.lean#L13) — regularity and cyclotomic coefficients
- [`Theorems/Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin.lean#L10) — the Galois structure of $`X(N)`$
- [`Theorems/Thm_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff.lean#L9) — the $`\Gamma_1`$ specialisation
- [`Theorems/Thm_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion.lean#L7) — reciprocity at the cusps
- [`Theorems/Thm_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean#L10) — spanning by Fricke-rationals
- [`P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean) — the ℘-route to $`\mathbb{C}/\Lambda \cong E(\mathbb{C})`$ of §1

mathlib (tag `v4.34.0`):

- [`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean) — `PeriodPair` (60), `weierstrassP` (268), `derivWeierstrassP_sq` (1075), pole order and periodicity
- [`NumberTheory/ModularForms/QExpansion.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/QExpansion.lean#L171) — `UpperHalfPlane.qExpansion h f`
- [`NumberTheory/ModularForms/CongruenceSubgroups.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L41) — `Gamma`, `Gamma0`, `Gamma1`
- [`NumberTheory/ModularForms/EisensteinSeries/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean) and [`NumberTheory/ModularForms/Discriminant.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/Discriminant.lean) — $`E_4`$, $`E_6`$, `discriminant`

Companion notes:

- [math/024 — Uniformization versus modular functions](024-uniformization-versus-modular-functions.md) — the $`\Lambda`$ dictionary and the level-one/$`X_0(N)`$ contrast
- [math/010 — Function field generation for X₀(N)](010-function-field-generation.md) — the $`\Gamma_0`$-type generation theorem
- [math/013 — The integral structure on Γ₁(N)](013-integral-structure-gamma1-basis.md) — the consumer of the rationality and integrality of §5
- [base/004 — The j-invariant](../base/004-the-j-invariant.md) — `LevelN.ring N` as the level-$`N`$ curve with Fricke coordinates
- [base/018 — Congruence subgroups and invariance](../base/018-congruence-subgroups-and-invariance.md) — $`\Gamma(N)`$, $`\Gamma_1(N)`$, $`\Gamma_0(N)`$ and their invariance

Background:

- G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton University Press, 1971, §6.1–6.2 — Fricke functions, the field of modular functions of level $`N`$, reciprocity.
- S. Lang, *Elliptic Functions*, 2nd ed., GTM 112, Springer, 1987, Ch. 6 §3 — the modular function field and its generators.
- F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer, 2005, §1.4 and §7.5 — $`q`$-expansions, $`X(N)`$.
- J. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, Springer, 1994, Ch. I — uniformization, lattices and the moduli interpretation.
