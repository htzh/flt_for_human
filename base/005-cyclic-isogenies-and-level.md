# Cyclic isogenies, congruence level, and the $`j`$-invariant

Fifth of the `base/` notes. [004](004-the-j-invariant.md) built the $`j`$-invariant and its
$`q`$-expansion; this note fixes the classical picture that the rest of the series reads:
complex tori as lattices, the cyclic isogenies out of a torus, and the level structure that
indexes them. §1 collects what a $`j`$-value determines — the moduli reading, and the
natural place to say more later about isomorphism classes of elliptic curves and their
models; §2 does the counting and builds the quotient dictionary. The **modular equation** on
top of that picture, its integrality and its splitting, is
[006](006-the-modular-equation.md), which consumes the dictionary below. The aim here is to
make sense of a sentence like

> "the $`p+1`$ cyclic $`p`$-isogenies out of $`E_\tau`$ have quotients
> $`E_{p\tau}`$ and $`E_{(\tau+b)/p}`$"

and of the surrounding words — *level*, *coset*, *Hauptmodul*, *line* — that note 010 uses
without pausing. We are **not** repeating the proof: the mathematics is the classical one,
the Lean fixes the order of the story, and it is quoted as a route map.

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
"slot"-indexed substitution $`q \mapsto \zeta_M^{\,ab} q^{a^2}`$ that
[006 §5](006-the-modular-equation.md#5-reading-note-010-a-short-dictionary) reads off a
coset label.

### What a point of $`Y(1)`$ determines: the curve, its model, and $`j`$

Everything above is analytic, through lattices and $`\mathbb{C}`$. From here on the words
are algebraic, and the Lean pins them down, so it is worth fixing them now. A point of
$`Y(1)`$ does **not** determine an equation. It determines an isomorphism class of
elliptic curves, and the code carries an explicit *model* — the coefficients — to
represent that class.

**A moduli point is a curve plus level data.** `Gamma0Pair N L` is the structure
([Def_ModularCurve_ModuliPoint.lean, lines 15–40](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ModuliPoint.lean#L15-L40)):
`toCurve : WeierstrassCurve L`, the model, i.e. the coefficients $`a_1,\dots,a_6`$;
`isElliptic : toCurve.IsElliptic`; and
`gen : toCurve.toAffine.Point` with `addOrderOf gen = N`, the level datum, a point whose
multiples are the cyclic subgroup $`\langle \mathrm{gen}\rangle`$ of order $`N`$. Two
such data are identified in `ModuliPoint N L` when a *variable change* carries one model
to the other and the generators differ by a unit $`k`$ coprime to $`N`$. So a moduli
point is an isomorphism class, and its level datum is the $`\mathcal{C}`$ of §2 — here a
subgroup of the point group of a curve, not a quotient lattice. For $`N = 1`$ the level
datum is trivial, so `ModuliPoint 1 L` is curves up to variable change.

**The map to the $`j`$-line is a function of the coefficients.** `WeierstrassCurve.j` is
the expression

$$j \\;=\\; \frac{c_4^3}{\Delta} \\;\in\\; R$$

([Weierstrass.lean, line 385](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean#L385)),
computed from the coefficients and unchanged by variable change. That invariance is what
lets it descend to `ModuliPoint.j : ModuliPoint N L → L`, which sends a point to the
$`j`$ of any model representing it. So a moduli point has a well-defined $`j`$, and
forgetting the model and the level structure lands on $`Y(1)`$ with coordinate $`j`$ —
the same coordinate as in the table above, now over any field instead of $`\mathbb{C}`$.

**A $`j`$-value determines the class, and one model is canonical.** For a field $`F`$ and
$`j \in F`$, `WeierstrassCurve.ofJ j` is an explicit curve with
`(WeierstrassCurve.ofJ j).j = j`
([ModelsWithJ.lean, lines 65–182](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/ModelsWithJ.lean#L65-L182)),
by cases on $`j`$:

$$j = 0: \quad Y^2 + Y = X^3, \qquad j = 1728: \quad Y^2 = X^3 + X,$$

$$j \ne 0, 1728: \quad Y^2 + (j-1728)XY \\;=\\; X^3 - 36(j-1728)^3X - (j-1728)^5 .$$

Conversely, if two elliptic curves over $`F`$ have the same $`j`$, then a *single*
variable change carries one to the other (`exists_variableChange_of_j_eq`,
[IsomOfJ.lean, line 333](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/IsomOfJ.lean#L333)).
So "a point of $`Y(1)`$ determines a curve" means exactly this: the isomorphism class is
determined, `ofJ` is a chosen representative of it, and every other model of that curve
is reached from `ofJ` by a variable change.

**Which model the code uses at a point.** Attaching `ofJ` everywhere would be awkward
locally, so the FLT development attaches a model adapted to the point and then proves it
is `ofJ` up to variable change. For $`j_0 \in \bar{\mathbb{Q}}`$:

- `nearCurve j₀ = WeierstrassCurve.ofJ (jNear j₀)` and
  `goodModel j₀ = scaleVC j₀ • nearCurve j₀`
  ([TatePoint.lean, line 21](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_TatePoint.lean#L21),
  [SpecialisationVocab.lean, lines 103 and 124](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_SpecialisationVocab.lean#L103-L124));
- and the identification `fibreVC j₀ • specialFibre (goodModel j₀) = WeierstrassCurve.ofJ j₀`
  ([SpecialisationBridge.lean, lines 181–185](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_SpecialisationBridge.lean#L181-L185)).

That last line is the pattern to expect throughout: explicit coefficients at the point,
plus an explicit variable change back to the canonical model.

**The function field of $`Y(1)`$.** Formally it is $`\mathbb{Q}(j)`$:
`jLineRingEquiv : RatFunc ℚ ≃+* ℚ⟮jq⟯`. The three distinguished points are named as
places — `jLinePlaceZero`, `jLinePlace1728`, `jLinePlaceInfty`
([JLinePlaces.lean, lines 36–58](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_JLinePlaces.lean#L36-L58)) —
the three values at which the curve has extra symmetry or degenerates.

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

where $`\langle x\rangle`$ is the cyclic subgroup generated by the single element $`x`$.
So $`\mathcal{C}`$ has $`p`$ elements inside the $`p^2`$-element group $`E_\tau[p]`$: it
is not all of $`E_\tau[p]`$. Since $`(m,n)`$ is read modulo $`p`$, we may take
$`(m,n) \in \mathbb{F}_p^2`$ nonzero; then $`(m,n)`$ and $`\lambda(m,n)`$ generate the
same $`\mathcal{C}`$ for every nonzero $`\lambda \in \mathbb{F}_p`$ — the scalar
ambiguity behind the word "lines" below.
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

**The quotients, explicitly.** An order-$`p`$ subgroup $`\mathcal{C} = \langle x\rangle`$
has a lattice $`L = \Lambda_\tau + \mathbb{Z}x \supsetneq \Lambda_\tau`$, with
$`E_\tau/\mathcal{C} \cong \mathbb{C}/L`$. Two facts about $`L`$ are all we use: it
depends on $`\mathcal{C}`$ alone, not on the generator chosen to present it, and its
index is $`[L : \Lambda_\tau] = p`$ — adjoining one point of order $`p`$ adds just one
coset of $`\Lambda_\tau`$. The quotient curve is read off a basis of $`L`$, up to
homothety: scaling a basis by $`\lambda \in \mathbb{C}^\times`$ leaves the torus
unchanged, since $`\mathbb{C}/\lambda L \cong \mathbb{C}/L`$. Thus

| line | $`\mathcal{C}`$ | $`L`$ | basis of $`L`$ | $`[L : \Lambda_\tau]`$ | quotient |
|---|---|---|---|---|---|
| $`n = 0`$ | $`\langle 1/p\rangle`$ | $`\Lambda_\tau + \tfrac1p\mathbb{Z}`$ | $`(\tfrac1p,\,\tau)`$ | $`p`$ | $`E_{p\tau}`$ |
| $`n \ne 0`$, $`b \in \mathbb{F}_p`$ | $`\langle(\tau+b)/p\rangle`$ | $`\Lambda_\tau + \mathbb{Z}\tfrac{\tau+b}{p}`$ | $`(1,\,\tfrac{\tau+b}{p})`$ | $`p`$ | $`E_{(\tau+b)/p}`$ |

Dividing a whole lattice by $`p`$ is not the same as adjoining a single point of order
$`p`$, and the two resulting expressions look almost identical:

$$\tfrac1p\Lambda_\tau \\;=\\; \mathbb{Z}\tfrac1p + \mathbb{Z}\tfrac1p\tau
  \\;\supsetneq\\; \Lambda_\tau, \qquad
  \bigl[\tfrac1p\Lambda_\tau : \Lambda_\tau\bigr] = p^2, \qquad
  \tfrac1p\Lambda_\tau/\Lambda_\tau \\;=\\; E_\tau[p],$$

$$\Lambda_\tau + \mathbb{Z}\tfrac1p \\;=\\; \mathbb{Z}\tfrac1p + \mathbb{Z}\tau
  \\;=\\; \tfrac1p\Lambda_{p\tau} \\;\supsetneq\\; \Lambda_\tau, \qquad
  \bigl[\Lambda_\tau + \mathbb{Z}\tfrac1p : \Lambda_\tau\bigr] = p, \qquad
  \bigl(\Lambda_\tau + \mathbb{Z}\tfrac1p\bigr)/\Lambda_\tau \\;=\\; \mathcal{C}.$$

The first is the whole $`p`$-torsion; only the second is one of the $`p+1`$ lines. So
the $`p+1`$ lines become $`p+1`$ curves of the same shape $`E_{\tau'}`$.

Thus the quoted sentence is a complete list:

$$E_\tau/\mathcal{C} \\;\in\\; \bigl\\{\\, E_{p\tau} \\,\bigr\\} \\;\cup\\;
  \bigl\\{\\, E_{(\tau+b)/p} \\;:\\; b = 0,1,\dots,p-1 \\,\bigr\\}.$$

The one curve $`E_{p\tau}`$ is the "line at infinity"; the other $`p`$ are indexed by
the slope $`b`$. In the nome $`q = e^{2\pi i\tau}`$ they read

$$j(p\tau) = j(q^p), \qquad
  j\\!\left(\tfrac{\tau+b}{p}\right) = j\\!\left(\zeta_p^{\\,b}\\,q^{1/p}\right),
  \qquad \zeta_p = e^{2\pi i/p},$$

which is where fractional powers of $`q`$ — and the roots of unity of the splitting formula
in [006 §3](006-the-modular-equation.md#3-splitting-of-the-modular-equation-and-the-cover-behind-it) —
first appear.

**Duality.** The quotient map $`E_\tau \to E_\tau/\mathcal{C}`$ has a dual isogeny
$`E_\tau/\mathcal{C} \to E_\tau`$, of the same degree, whose kernel is the dual subgroup. So
"being $`p`$-isogenous" is a symmetric relation; this is the source of the symmetry
$`\Phi_p(X,Y) = \Phi_p(Y,X)`$ used in
[006 §1](006-the-modular-equation.md#1-the-modular-polynomial).

**General level.** Replacing "order $`p`$" by "cyclic of order $`N`$" gives the same
story with $`\psi(N)`$ in place of $`p+1`$. The number of cyclic order-$`N`$
subgroups of $`(\mathbb{Z}/N)^2`$ is the Dedekind function

$$\psi(N) \\;=\\; \sum_{\substack{d \mid N \\\\ d\\ \text{squarefree}}} \frac{N}{d}
  \\;=\\; N \prod_{p \mid N}\Bigl(1 + \frac1p\Bigr),$$

the index $`[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)]`$. For $`N = p`$ this is
$`p+1`$, and the $`p+1`$ subgroups above are the first case.

## 3. Links

Companion notes:

- [004 — The j-invariant](004-the-j-invariant.md) — the series `jq` and its integral $`q`$-expansion
- [006 — The modular equation](006-the-modular-equation.md) — integrality and splitting of $`\Phi_N`$, which use the quotient dictionary of §2
- [math/010 §3](../math/010-function-field-generation.md#3-the-modular-polynomial-and-the-roots-of-the-modular-equation) — the section this pair of notes supplements

Background:

- J. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, Springer 1994, Ch. I — complex tori, isogenies, and the $`j`$-invariant.
- F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer 2005, Ch. 1 — congruence subgroups, $`X_0(N)`$, and functions on it.
