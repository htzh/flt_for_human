# Iwasawa theory at the archimedean place: the decomposition, the compact factor, and the estimates

Twenty-eighth of the `math/` notes. The Deligne–Serre column's frontier reaches the archimedean
half of the automorphic `GL₂` layer through a self-contained analytic development that the FLT pin
files under `AutomorphicForm.ComplexIwasawa` and `AutomorphicForm.RealIwasawa`. This note explains
what that development *is*: the Iwasawa decomposition over $`\mathbb{R}`$ and $`\mathbb{C}`$, the
compact factor it produces, and the estimates on that factor and its radial length which the
Rankin–Selberg / Whittaker integrals consume. The mathematics is §1–§6; the Lean map, deliberately
short, is §7.

The word "Iwasawa" carries two meanings in this area — the **decomposition** of a reductive group
and **Iwasawa theory** in the sense of $`\mathbb{Z}_p`$-extensions — and the pin uses only the
first, so §1 separates them before the mathematics begins.

Companions: [019-deligne-serre-weight-one.md](019-deligne-serre-weight-one.md) (the theorem whose
gate these estimates stand behind), [015-weight-two-hecke-periods.md](015-weight-two-hecke-periods.md)
(the period/Whittaker layer of the same family), [011-tate-module.md](011-tate-module.md) (the
$`\ell`$-adic side), [../base/012-adeles-and-automorphic-representations.md](../base/012-adeles-and-automorphic-representations.md)
(the adèlic dictionary) and [../base/022-haar-measure.md](../base/022-haar-measure.md) (the measure
the integrals below are taken against). The port record is
[../lean/topics/automorphicForm/TOPIC-iwasawa-analytic-core.md](../lean/topics/automorphicForm/TOPIC-iwasawa-analytic-core.md).

## 1. Two things called Iwasawa

**The Iwasawa decomposition.** For a connected reductive group $`G`$ over a local field, or a
semisimple real Lie group, the multiplication map

$$N \times A \times K \longrightarrow G, \qquad (n, a, k) \longmapsto n a k ,$$

is a diffeomorphism (a homeomorphism over a $`p`$-adic field). Here $`K`$ is a maximal compact
subgroup, $`A`$ a maximal split torus, and $`N`$ the unipotent radical of a Borel subgroup. For
$`\mathrm{GL}_2`$ it is the familiar triangular-times-compact factorisation
$`G = B K`$ with $`B = N A`$ the upper triangular (Borel) subgroup. It is the Lie-group analogue of
the Gram–Schmidt process, and it is what makes harmonic analysis on $`G`$ tractable: the compact
part carries unitary representations, the torus part carries characters, and the unipotent part is
where the Fourier transform lives.

**Iwasawa theory.** Separately, "Iwasawa theory" denotes the study of $`\mathbb{Z}_p`$-extensions
$`F_\infty/F`$, the Iwasawa algebra $`\Lambda = \mathbb{Z}_p[[\Gamma]]`$ with
$`\Gamma \cong \mathbb{Z}_p`$, Iwasawa's theorem that the $`p`$-parts of the class groups in a
$`\mathbb{Z}_p`$-tower obey a fixed polynomial, and the Iwasawa main conjecture relating the
$`p`$-adic $`L`$-function to the characteristic ideal of a Selmer group. That theory belongs to the
Galois-deformation side of modularity; it is **not** what this note, or the port it describes, is
about. When a pin file says `Iwasawa` in this column it always means the decomposition.

## 2. The decomposition for `GL₂(ℝ)` and `GL₂(ℂ)`

We follow the pin, which works with one specific translate rather than the decomposition in
abstract form. Fix a field $`K = \mathbb{R}`$ or $`\mathbb{C}`$, a matrix

$$g = \begin{pmatrix} g_{00} & g_{01} \\ g_{10} & g_{11} \end{pmatrix} \in \mathrm{GL}_2(K),$$

the Weyl element $`w = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}`$ and the upper unipotent
$`n(z) = \begin{pmatrix} 1 & z \\ 0 & 1 \end{pmatrix}`$ with $`z \in K`$ (for $`K = \mathbb{R}`$ we
write $`x`$ for the real variable). The product is

$$w \, n(z) \, g = \begin{pmatrix} g_{10} & g_{11} \\ g_{00} + z g_{10} & g_{01} + z g_{11} \end{pmatrix},$$

so its **bottom row** is exactly the pair the pin calls $`P(z)`$ and $`Q(z)`$:

$$P(z) = g_{00} + z g_{10}, \qquad Q(z) = g_{01} + z g_{11}.$$

The bottom row is nonzero because $`\det g \neq 0`$: if both entries vanished the determinant
would vanish. This is the only place the hypothesis $`\det g \neq 0`$ enters, and it is what keeps
the radial length of the next paragraph bounded away from zero.

**The radial length and the compact factor.**

- Over $`\mathbb{C}`$, with $`P, Q : \mathbb{C} \to \mathbb{C}`$ as above,

$$\operatorname{radC}(g, z) = \sqrt{\lvert P(z) \rvert^2 + \lvert Q(z) \rvert^2}, \qquad
k_{\mathbb{C}}(g,z) = \frac{1}{\operatorname{radC}(g,z)}
  \begin{pmatrix} \overline{Q(z)} & -\overline{P(z)} \\ P(z) & Q(z) \end{pmatrix}.$$

The matrix $`k_{\mathbb{C}}`$ has orthogonal columns of norm $`1`$ and determinant
$`(\lvert P\rvert^2 + \lvert Q\rvert^2)/\operatorname{radC}^2 = 1`$, hence lies in $`\mathrm{SU}(2)`$.
This is the pin's `kC`.

- Over $`\mathbb{R}`$, with the same $`P, Q`$ read as real linear functions and
$`r(g,x) = \sqrt{P(x)^2 + Q(x)^2}`$,

$$k_{\mathbb{R}}(g,x) = \frac{1}{r(g,x)}
  \begin{pmatrix} Q(x) & -P(x) \\ P(x) & Q(x) \end{pmatrix}
  = \begin{pmatrix} \cos\theta & -\sin\theta \\ \sin\theta & \cos\theta \end{pmatrix}
  \quad \text{with } \cos\theta = \frac{Q(x)}{r}, \ \sin\theta = \frac{P(x)}{r}.$$

So the real compact factor is a rotation, and the whole analytic content of the real case is the
behaviour of the angle $`\theta(g,x)`$; the pin states it inline, without naming the angle, in the
`RealIwasawa` wrappers.

**The decomposition itself.** Because $`k_{\mathbb{C}}`$ (resp. $`k_{\mathbb{R}}`$) is invertible
and unitary (resp. orthogonal), the translate factors as

$$w \, n(z) \, g = b(g,z) \cdot k(g,z), \qquad
b(g,z) = \begin{pmatrix}
  -\det g / \operatorname{radC} &
  \bigl(g_{10}\overline{P} + g_{11}\overline{Q}\bigr)/\operatorname{radC} \\
  0 & \operatorname{radC}
\end{pmatrix},$$

an upper triangular (Borel) factor. Checking determinants,
$`\det b = -\det g`$ and $`\det k = 1`$, while $`\det(w n(z) g) = -\det g`$: the factorisation is
consistent, and in particular the Iwasawa decomposition of this translate is *explicit* — no
Gram–Schmidt is needed, only the division by the radial length. That explicitness is why the pin
can estimate the compact factor by hand, without the structure theory of reductive groups.

## 3. The radial length is comparable to the distance to infinity

Write $`K = \mathbb{R}`$ and $`x`$ for the variable first. Then

$$r(g,x)^2 = (g_{00} + x g_{10})^2 + (g_{01} + x g_{11})^2
        = (g_{10}^2 + g_{11}^2)\, x^2 + 2(g_{00}g_{10} + g_{01}g_{11})\, x + (g_{00}^2 + g_{01}^2),$$

a quadratic polynomial whose leading coefficient $`\lambda(g) = g_{10}^2 + g_{11}^2`$ is positive
(bottom row nonzero) and whose discriminant is $`-(\det g)^2 \lt 0`$ by the identity
$`(g_{00}g_{10} + g_{01}g_{11})^2 - (g_{10}^2+g_{11}^2)(g_{00}^2+g_{01}^2) = -(\det g)^2`$.
A positive definite quadratic form in one variable is bounded above and below by positive constants
times $`1 + x^2`$, uniformly on compact sets of invertible matrices:

$$c(\mathcal{G})^{-1}(1 + x^2) \le r(g,x)^2 \le c(\mathcal{G})(1 + x^2),
  \qquad g \in \mathcal{G} \text{ compact}, \ \det \neq 0 .$$

Over $`\mathbb{C}`$ the same computation in the two real coordinates of $`z = u + iv`$ says that
$`\operatorname{radC}(g,z)^2`$ is a positive definite Hermitian form in $`(u,v)`$, so

$$\operatorname{radC}(g,z)^2 \asymp 1 + \lvert z \rvert^2$$

with constants uniform on compacta of invertible matrices.

Two immediate consequences, both headlines in the pin:

- **Smoothness.** A positive definite quadratic form has no real zeros, so $`r`$ (resp.
  $`\operatorname{radC}`$) is smooth and strictly positive, and so are the entries of the compact
  factor.
- **Integrability.** On $`\mathbb{R}`$ the integral $`\int_{\mathbb{R}} r^{-s}\,dx`$ converges at
  infinity exactly when $`s \gt 1`$, because $`r^{-s} \asymp (1+x^2)^{-s/2}`$ and
  $`\int_1^\infty x^{-s}\,dx`$ converges iff $`s \gt 1`$. On $`\mathbb{C}`$, viewed as
  $`\mathbb{R}^2`$,

$$\int_{\mathbb{C}} \operatorname{radC}(g,z)^{-\kappa}\,dz \lt \infty
  \iff \kappa \gt 2 ,$$

the exponent $`2`$ being the real dimension; this is why every complex statement in the pin carries
$`\kappa \gt 2`$ (or $`\operatorname{Re} u \gt 2`$), while the real statements carry the half-plane
$`\operatorname{Re} u \gt 1`$. The half-planes are not technicalities: they are the exact
convergence region of the archimedean weight, and the analytic continuation past them is the whole
point of §5.

## 4. Symbol bounds for the weight `rad^{-u}`

The archimedean weight attached to the compact factor is the complex power
$`z \mapsto (\operatorname{radC}(g,z) \cdot \mathbb{C})^{-u}`$ for $`u \in \mathbb{C}`$, and the
input to every Fourier estimate is that this weight is a **symbol of order** $`\operatorname{Re} u`$:
smooth, with every derivative dominated by the undifferentiated majorant.

**Proposition (symbol bound).** For every $`n`$ and every compact set $`\mathcal{G}`$ of invertible
matrices and compact $`U \subset \mathbb{C}`$ there is $`K \gt 0`$ with

$$\bigl\lVert D^n_z \bigl(\operatorname{radC}(g,z)^{-u}\bigr) \bigr\rVert
  \le K \cdot \operatorname{radC}(g,z)^{-\operatorname{Re} u},
  \qquad g \in \mathcal{G}, \ u \in U, \ z \in \mathbb{C}.$$

*Why.* Write $`\operatorname{radC}^{-u} = \exp(-u \log \operatorname{radC})`$. Since
$`\operatorname{radC}^2`$ is a positive definite quadratic form,
$`\log \operatorname{radC} = \tfrac12 \log(\text{quadratic form})`$ has derivatives of every order
bounded by constants depending only on the compact set of matrices (each derivative of
$`\log `$ of a positive definite form is a rational function whose numerator is bounded and whose
denominator is bounded below by a positive constant). The chain rule then writes
$`D^n \operatorname{radC}^{-u}`$ as $`\operatorname{radC}^{-u}`$ times a polynomial in $`u`$ and
those bounded derivatives, and $`\lvert \operatorname{radC}^{-u}\rvert = \operatorname{radC}^{-\operatorname{Re} u}`$. This is the pin's
`contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact`, and the real case is
identical with $`\operatorname{radC}`$ replaced by $`r`$ and the variable $`z`$ by $`x`$.

The same computation with $`u`$ fixed, and the smoothness of the entries of $`k`$ in §2, gives the
two *compact-factor* headlines: the entries of $`k_{\mathbb{C}}(g,\cdot)`$ and
$`k_{\mathbb{R}}(g,\cdot)`$ are $`C^\infty`$, and all their iterated derivatives are bounded —
pointwise in $`g`$ (`contDiff_and_exists_bound_iteratedFDeriv_k{C,R}_apply`), and uniformly as
$`g`$ ranges over a compact set of invertible matrices
(`exists_forall_bound_iteratedFDeriv_k{C,R}_apply_of_isCompact`). Uniformity in $`g`$ is what an
adelic argument needs, because the archimedean place is one factor among many and the global
estimate must not depend on which $`g`$ the local computation is applied to.

## 5. Fourier decay, and the Whittaker integral

The reason to want symbol bounds is that derivatives in the spatial variable buy decay in the
Fourier variable, by integration by parts.

**The coercive Fourier bound.** Let $`V, W`$ be real normed spaces and
$`L : V \to W \to \mathbb{R}`$ a continuous bilinear pairing that is *coercive*: there is
$`c \gt 0`$ with

$$\forall w \in W \ \exists v \in V, \quad \lVert v \rVert \le 1
  \ \text{ and } \ c \lVert w \rVert \le \lvert L(v,w) \rvert .$$

For $`f : V \to E`$ of class $`C^n`$ with the iterated derivative norms integrable, the Fourier
integral against the standard additive character $`\mathbf{e}(t) = e^{2\pi i t}`$ obeys

$$(c \lVert w \rVert)^n \, \Bigl\lVert \int_V f(v)\, \mathbf{e}\bigl(-L(v,w)\bigr)\, dv
  \Bigr\rVert \le 2^n \sum_{j=0}^{n} \int_V \lVert D^j f(v) \rVert \, dv .$$

The proof is $`n`$ integrations by parts against the coercive direction: the boundary terms vanish
because $`f`$ and its derivatives are integrable, and each integration by parts produces a factor
$`L(v,w)/(c\lVert w\rVert)`$ of modulus at most $`1`$. This is the pin's
`pow_mul_norm_fourierIntegral_le_of_coercive`, and it is a completely general measure/Fourier fact,
with no arithmetic or automorphic input.

**Rapid decay of the weight transform.** Take $`V = W = \mathbb{C}`$, $`L(v,w) = \operatorname{Re}(v \bar w)`$
(or its real analogue), and $`f(z) = \operatorname{radC}(g,z)^{-u} P(z)`$ with $`P`$ smooth and all
its derivatives bounded. The symbol bound of §4 bounds $`\int \lVert D^j f \rVert`$ by
$`\sum_i \binom{j}{i} K_i C_{j-i} \int \operatorname{radC}^{-\operatorname{Re} u}`$, which is finite
as soon as $`\operatorname{Re} u \gt 2`$ by §3. Feeding that into the coercive bound with $`n = N`$
gives, for every $`N`$,

$$\Bigl\lVert \int_{\mathbb{C}} \operatorname{radC}(g,z)^{-u} P(z)\,
  e^{-i L(z,\xi)}\, dz \Bigr\rVert \le C(g,u,P,N)\,(1 + \lVert \xi \rVert)^{-N}.$$

This is the pin's `norm_fourierIntegral_cpow_radC_mul_le_polyDecay` — faster-than-any-polynomial
decay in the frequency variable, uniform in $`g`$ over compacta in the uniform version
`exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact`. The real case is the
same with $`\operatorname{radC}`$ replaced by $`r(x) = \sqrt{(g_{00}+xg_{10})^2 + (g_{01}+xg_{11})^2}`$
and the half-plane $`\operatorname{Re} u \gt 1`$.

**The Jacquet (Whittaker) integral.** The headline that packages all of this is the archimedean
local Whittaker function, written as an integral over the additive group,

$$j_{a,b}(w, \zeta) = \int_{\mathbb{C}} z^{a} \bar z^{b} (1 + \lvert z \rvert^2)^{-w}
  e^{-4\pi i \operatorname{Re}(\zeta z)}\, dz
  \qquad (a,b \in \mathbb{N}, \ w \in \mathbb{C}, \ \zeta \in \mathbb{C}),$$

for the complex place, and

$$j_{k}(w, t) = \int_{\mathbb{R}} \Bigl(\frac{x - i}{\sqrt{1 + x^2}}\Bigr)^{k}
  (1 + x^2)^{-w} e^{-2\pi i\, t x}\, dx
  \qquad (k \in \mathbb{Z}, \ w \in \mathbb{C}, \ t \in \mathbb{R})$$

for the real place. The half-plane of absolute convergence is $`\operatorname{Re} w \gt (a+b)/2 + 1`$
in the complex case (the polynomial factor $`z^a \bar z^b`$ has absolute value
$`\lvert z\rvert^{a+b}`$, and the weight contributes $`\lvert z\rvert^{-2\operatorname{Re} w}`$, so
convergence needs $`2 \operatorname{Re} w \gt a + b + 2`$) and $`\operatorname{Re} w \gt 1/2`$ in the
real case (where the weight is $`(\sqrt{1+x^2})^{-2w}`$, modulo the unitary factor
$`(x-i)/\sqrt{1+x^2}`$). On that half-plane the integral

- is continuous in the pair $`(w,\zeta)`$ (dominated convergence, the §3 integrability),
- is holomorphic in $`w`$ (differentiation under the integral sign, Cauchy–Riemann; the
  $`w`$-derivative brings down a factor $`-\log(1+\lvert z\rvert^2)`$, still dominated), and
- decays faster than any polynomial in $`\zeta`$, uniformly on compacta in the strip (the Fourier
  decay of §4 applied to the weight $`z^a\bar z^b(1+\lvert z\rvert^2)^{-w}`$).

These are the pin's `continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral` in the
two namespaces. The statement is exactly the local input the global theory wants: a Whittaker
function that is entire in the spectral parameter and of rapid decay in the additive variable,
uniformly on vertical strips.

## 6. Where the estimate is used

Three consumers, in increasing order of depth.

**Eisenstein series and their Fourier expansion.** The constant term and the Fourier coefficients
of an Eisenstein series are built from archimedean Whittaker integrals. The half-plane statement
gives the absolute convergence and holomorphy of the local factor; the rapid decay is what lets one
sum the Fourier expansion and bound the growth, and the uniformity on strips is what makes the
Eisenstein series *moderate* uniformly in the spectral parameter.

**Weyl–unipotent integrals.** The bound
`AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary` estimates
integrals of the form $`\int w n(z) g \cdot \chi(z)\, dz`$ against an additive character, for a
unitary matrix coefficient. The two Iwasawa facts enter together: the **unitary** compact factor is
absorbed by the unitary vector, and the **triangular** (Borel) factor is controlled by the estimates
of §4–§5 applied to its radial length. This is the pin's own comment on
`kC_mem_specialUnitaryGroup` and `weyl_mul_unipotent_mul_eq_borel_mul_kC`.

**The Rankin–Selberg second moment.** The deepest consumer is the analytic engine of the
Deligne–Serre weight-one column's Gate 1: the bound
`DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen` on
$`\sum_n \lvert a_n\rvert^2 n^{-s}`$ for a weight-one Hecke eigenform. That bound is proved by a
Rankin–Selberg-type integral of the cusp form against itself, and the archimedean factor of that
integral is exactly the local estimate above: after unfolding, the archimedean contribution is an
integral of $`\lvert W(g)\rvert^2`$ against the weight $`(1 + \lvert z\rvert^2)^{-w}`$, and its
convergence and polynomial-in-$`\operatorname{Im} w`$ bounds are the analytic input at the infinite
place. The two gates of [019](019-deligne-serre-weight-one.md) §7 wait on this; the archimedean
estimates of this note are the part of the gate that is *already* self-contained and provable today.

## 7. The Lean map

The pin's archimedean Iwasawa development lives in twenty `S_` files, nine under
`AutomorphicForm.ComplexIwasawa` and four under `AutomorphicForm.RealIwasawa` in the Deligne–Serre
cone (a further three complex files sit outside it). The 13 in-cone nodes, their two namespaces and
the port's two-wave engine/façade structure are in the topic note; in one sentence: the six
complex and four real kernels are the statements above, the shared generic Fourier bound of §5 is
homed once in `MeasureTheory/FourierDecay.lean`, the complex definition module
`Def_AutomorphicForm_ComplexIwasawa` (the `botP`/`botQ`/`radC`/`kC` of §2) is homed whole, and the
real half has no definition module because its statements spell the rotation out inline.

Two conventions are worth recording here because they are mathematics, not engineering. First,
**the complex and real halves are parallel developments, not specialisations of one another**: the
complex compact factor is a $`\mathrm{SU}(2)`$-matrix whose entries involve $`\overline{P}`$ and
$`\overline{Q}`$, the real one is a rotation, and the pin proves the two sets of estimates
separately (the shared surface is a single generic Fourier lemma). Second, **the exponents are not
interchangeable**: the complex place has real dimension $`2`$ and so needs $`\kappa \gt 2`$, the
real place dimension $`1`$ and so needs $`\operatorname{Re} u \gt 1`$; a port that unified the two
would have to take the worse bound on each, which is why the pin keeps them apart.

## References

- K. Iwasawa, *On some types of topological groups*, Ann. of Math. **50** (1949), 507–558 — the
  decomposition $`G = NAK`$.
- A. Bump, *Automorphic Forms and Representations*, Cambridge Studies in Advanced Mathematics 55,
  CUP, 1997 — the archimedean Iwasawa decomposition for $`\mathrm{GL}_2`$ and the Whittaker/Jacquet
  integrals, which the pin cites for these nodes.
- H. Jacquet, *Fonctions de Whittaker associées aux groupes de Chevalley*, Bull. Soc. Math. France
  **95** (1967), 243–309 — the Whittaker integral and its analytic continuation.
- A. Weil, *Fonctions zêta des algèbres simples*, and the Rankin–Selberg method: see
  [019-deligne-serre-weight-one.md](019-deligne-serre-weight-one.md) §2 for the weight-one context.
- J.-P. Serre, *Représentations linéaires des groupes finis*, for the Artin side of the Deligne–Serre
  correspondence; the $`\mathbb{Z}_p`$-extension Iwasawa theory contrasted in §1 is
  L. Washington, *Introduction to Cyclotomic Fields*, GTM 83, Ch. 13.
