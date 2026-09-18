# Cyclic isogenies, congruence level, and the $`j`$-invariant

Fifth of the `base/` notes. [004](004-the-j-invariant.md) built the $`j`$-invariant and its
$`q`$-expansion; this note fixes the classical picture that the rest of the series reads:
complex tori as lattices, the cyclic isogenies out of a torus, and the level structure that
indexes them. §1 collects what a $`j`$-value determines — the moduli reading, and the
natural place to say more later about isomorphism classes of elliptic curves and their
models; §2 does the counting and builds the quotient dictionary; §3 walks the resulting
four-sheeted cover $`X_0(3) \to X(1)`$ in the $`\tau`$-picture and catalogues its
monodromy. The **modular equation** on
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

**Duality.** The relation "is $`p`$-isogenous to" is symmetric, and the lattice picture
shows it in two steps. Starting from $`\Lambda_\tau = \langle 1, \tau\rangle`$, adjoin a
single point of order $`p`$:

$$\langle 1, \tau\rangle \\;\subset\\; \langle \tfrac1p, \tau\rangle \\;\subset\\;
  \langle \tfrac1p, \tfrac{\tau}{p}\rangle \\;=\\; \tfrac1p\Lambda_\tau .$$

Each inclusion has index $`p`$, so each is a cyclic $`p`$-isogeny. The first is
$`E_\tau \to E_{p\tau}`$ (the line $`n = 0`$ of the table, rescaled by $`p`$). The second
is a $`p`$-isogeny *out of* $`E_{p\tau}`$, and its target is
$`\mathbb{C}/\tfrac1p\Lambda_\tau`$, homothetic to $`\mathbb{C}/\Lambda_\tau = E_\tau`$
(rescale by $`p`$). So the second map returns to $`E_\tau`$, its kernel is generated by
the image of $`\tau/p`$, and the two steps compose to multiplication by $`p`$ (kernel
$`E_\tau[p]`$, degree $`p^2`$). That returning map is the **dual isogeny**.

In general, let $`\mathcal{C} = L/\Lambda_\tau`$ with $`L \supset \Lambda_\tau`$ of index
$`p`$, and put $`E' = E_\tau/\mathcal{C} = \mathbb{C}/L`$. The kernel of the dual isogeny
is the image of the whole $`p`$-torsion,

$$\mathcal{C}^\perp \\;=\\; \phi\bigl(E_\tau[p]\bigr) \\;=\\;
  \tfrac1p\Lambda_\tau \big/ L \\;\le\\; E'[p], \qquad
  \\#\mathcal{C}^\perp \\;=\\; p ,$$

and quotienting by it returns to the starting curve,

$$E'\big/\mathcal{C}^\perp \\;=\\; \mathbb{C}\big/\tfrac1p\Lambda_\tau \\;\cong\\;
  \mathbb{C}/\Lambda_\tau \\;=\\; E_\tau ,$$

the isomorphism again being rescaling by $`p`$. So every cyclic $`p`$-isogeny
$`\phi : E_\tau \to E'`$ has a dual $`\widehat\phi : E' \to E_\tau`$ of the same degree
$`p`$, with $`\widehat\phi \circ \phi = [p]`$. Concretely: the dual of the line
$`n = 0`$ isogeny of $`E_\tau`$ is the slope-$`0`$ isogeny of $`E_{p\tau}`$ (its kernel
is generated by $`\tau/p \in E'[p]`$, which the rescaling carries to the line
$`\langle \tau\rangle = \langle (p\tau + 0)/p\rangle`$), and the dual of the slope-$`b`$
isogeny of $`E_\tau`$ is the line $`n = 0`$ isogeny of $`E_{(\tau+b)/p}`$ (kernel
$`\langle 1/p\rangle`$, and indeed
$`\mathbb{C}/\langle 1/p, (\tau+b)/p\rangle \cong E_\tau`$ after rescaling by $`p`$). So
the $`p+1`$ quotients form one class under duality: the table above, read backwards, is
the same table. This is the source of the symmetry $`\Phi_p(X,Y) = \Phi_p(Y,X)`$ used in
[006 §1](006-the-modular-equation.md#1-the-modular-polynomial).

**General level.** Replacing "order $`p`$" by "cyclic of order $`N`$" gives the same
story with $`\psi(N)`$ in place of $`p+1`$. The number of cyclic order-$`N`$
subgroups of $`(\mathbb{Z}/N)^2`$ is the Dedekind function

$$\psi(N) \\;=\\; \sum_{\substack{d \mid N \\\\ d\\ \text{squarefree}}} \frac{N}{d}
  \\;=\\; N \prod_{p \mid N}\Bigl(1 + \frac1p\Bigr),$$

the index $`[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)]`$. For $`N = p`$ this is
$`p+1`$, and the $`p+1`$ subgroups above are the first case.

## 3. The four sheets over $`\tau`$: monodromy of $`X_0(3) \to X(1)`$

§2 listed the four order-$`3`$ subgroups of $`E_\tau`$ and their quotients. Those same
four objects are the four points of $`X_0(3)`$ above the point $`[\tau]`$ of $`X(1)`$:
the cover $`X_0(3) \to X(1)`$ has four sheets, and away from the cusps and the two
elliptic points they sit over $`[\tau]`$ distinctly. This section walks that cover in
$`\tau`$ alone — no function fields, no $`q`$-expansions, only points of
$`\mathbb{H}`$, lattices, and paths.

**Base point, loop, sheets.** Fix a generic $`\tau`$ and $`\gamma`$ in
$`\mathrm{SL}_2(\mathbb{Z})`$. By §1, $`j(\gamma\tau) = j(\tau)`$: the marked curves
$`E_\tau`$ and $`E_{\gamma\tau}`$ occupy the *same* point of $`X(1)`$ even though they
are different lattices, so the image of a path in $`\mathbb{H}`$ from $`\tau`$ to
$`\gamma\tau`$ is a loop in $`X(1)`$ based at $`[\tau]`$. The matrix $`\gamma`$ does move
the marked curve — it changes the period basis — and $`j`$ is exactly what forgets that;
the path closes because $`j`$ does not see the change. Meanwhile each of the four
subgroups $`\mathcal{C} \le E_\tau[3]`$ is a point of $`X_0(3)`$ above $`[\tau]`$; as
$`\tau`$ travels along the path the four points travel with it, and when the base point
returns to $`[\tau]`$ the four return *as a set*, generally permuted. That permutation,
computed below, is the monodromy of the cover.

**The four sheets, labelled.** A subgroup of order $`3`$ in
$`E_\tau[3] \cong \mathbb{F}_3^2`$ is a line $`\langle(m,n)\rangle`$; §2 gives the
quotient it cuts out. Label each sheet by that quotient:

| slot | line | kernel | quotient |
|---|---|---|---|
| $`\infty`$ | $`(1,0)`$ | $`\langle 1/3\rangle`$ | $`E_{3\tau}`$ |
| $`b = 0,1,2`$ | $`(b,1)`$ | $`\langle(\tau+b)/3\rangle`$ | $`E_{(\tau+b)/3}`$ |

A line with $`n \ne 0`$ is a scalar multiple of $`(m/n,1)`$ and carries the slot
$`b = m/n`$ in $`\mathbb{F}_3`$; the line $`(m,0)`$ carries the slot $`\infty`$. So the
four points above $`[\tau]`$ have quotient curves $`E_{3\tau}`$ and
$`E_{(\tau+b)/3}`$ — the four images of $`[\tau]`$ under the $`3`$-isogeny
correspondence. The four sheets are also the four cosets of $`\Gamma_0(3)`$ in
$`\mathrm{SL}_2(\mathbb{Z})`$ — the same count,
$`[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(3)] = \psi(3) = 4`$ (`Gamma0_index`,
[Thm_ModularCurve_Gamma0_index.lean, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_Gamma0_index.lean#L10)) —
which the code lists as `primCosetReps 3`
([Def_ModularCurve_PrimCosetReps.lean, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PrimCosetReps.lean#L8)).

**How a sheet moves.** Write $`\gamma = [[a,b],[c,d]]`$ and let $`\tau(t)`$,
$`0 \le t \le 1`$, run from $`\tau`$ to $`\gamma\tau`$, chosen to avoid the elliptic
points (which one may do within a homotopy class). A lift of the loop is a continuous
choice of line $`\mathcal{L}(t) \le E_{\tau(t)}[3]`$; the simplest choice keeps the
coordinates fixed in the moving basis $`(1,\tau(t))`$:

$$\mathcal{L}_{(m,n)}(t) \\;=\\; \langle (m + n\tau(t))/3 \rangle .$$

At $`t = 1`$ this line lies in $`E_{\gamma\tau}`$, and to name it back in the fixed curve
$`E_\tau`$ we use the explicit isomorphism of §1, multiplication by
$`\lambda = c\tau + d`$:

$$\lambda\Lambda_{\gamma\tau} \\;=\\; \mathbb{Z}(c\tau+d) + \mathbb{Z}(a\tau+b)
  \\;=\\; \Lambda_\tau .$$

Pushing the generator across it,

$$\lambda\cdot\frac{m + n\gamma\tau}{3} \\;=\\;
  \frac{m(c\tau+d) + n(a\tau+b)}{3} \\;=\\;
  \frac{(md+nb) + (mc+na)\tau}{3},$$

so on coordinates the loop acts by

$$(m,n) \\;\longmapsto\\; (dm + bn,\\; cm + an),$$

that is, by the matrix $`[[d,b],[c,a]]`$, read modulo $`3`$. Since $`-1`$ acts trivially
on lines, $`\gamma`$ and $`-\gamma`$ give the same permutation, and the rule only sees
$`\gamma`$ modulo $`3`$ up to sign: the loops that act trivially are those with
$`\gamma \equiv \pm I \pmod 3`$.

**The picture to keep: sheets are functions of $`\tau`$.** The path is the primary
object. Let $`\tau`$ vary slowly along a path in $`\mathbb{H}`$ from $`\tau`$ to
$`\gamma\tau`$ — not itself closed, but with closed image in $`X(1)`$ — and let it track
the loop. Pull the cover back to $`\mathbb{H}`$: since $`\mathbb{H}`$ is simply
connected the pullback is trivial — four globally labelled sheets, indexed by the four
cosets $`\Gamma_0(3)\backslash\mathrm{SL}_2(\mathbb{Z})`$. So **a sheet is a function of
the base point**: as $`\tau`$ moves, the sheet over it carries its value $`q(\tau(t))`$
along, and the only move available is to substitute the new value of $`\tau`$. Applying
the Möbius map $`\gamma`$ to a value is not a move in this picture. And since
$`\mathbb{H}`$ is simply connected, the endpoint of the lift — the permutation — depends
only on the homotopy class of the loop in $`X(1)`$, that is, only on $`\gamma`$.

**A shorter route to the same permutation.** The four sheets can also be followed by
their quotient values alone, with no lattice basis in sight. A sheet over the base
$`\tau`$ has value $`q(\tau) \in \{3\tau,\ (\tau+b)/3\}`$; keeping coordinates fixed in
the moving basis means that the same sheet carries the value $`q(\tau(t))`$ at time
$`t`$, so at the end it carries $`q(\gamma\tau)`$ — substitute
$`\tau \mapsto \gamma\tau`$ in the expression, so $`3\tau \mapsto 3\gamma\tau`$ and
$`(\tau+b)/3 \mapsto (\gamma\tau+b)/3`$. Values are read up to
$`\mathrm{SL}_2(\mathbb{Z})`$: $`q`$ and $`q'`$ name the same sheet exactly when
$`\mathbb{Z} + \mathbb{Z}q`$ and $`\mathbb{Z} + \mathbb{Z}q'`$ are homothetic, that is
$`q' = \gamma'q`$; for generic $`\tau`$ the four values are distinct, so this does name
a sheet. Two instances, matching the table below:

- $`\gamma = [[1,1],[0,1]]`$: the value $`3(\tau+1) = 3\tau+3`$ has lattice
  $`\mathbb{Z} + \mathbb{Z}(3\tau+3) = \mathbb{Z} + 3\mathbb{Z}\tau
  = \mathbb{Z} + \mathbb{Z}\cdot 3\tau`$, so $`\infty`$ is fixed; and
  $`(\tau+b)/3`$ is already the standard value for slot $`b+1`$, so $`b \mapsto b+1`$;
- $`\gamma = [[0,-1],[1,0]]`$: the value $`3\tau`$ becomes $`-3/\tau`$, and
  $`-3/\tau = [[0,1],[-1,0]]\cdot(\tau/3)`$ names slot $`0`$, so $`\infty \mapsto 0`$;
  the value $`\tau/3`$ becomes $`-1/(3\tau)`$, which scaled by $`-3\tau`$ is
  $`\mathbb{Z} + \mathbb{Z}\cdot 3\tau`$, so $`0 \mapsto \infty`$; and
  $`(\tau+1)/3`$ becomes $`(\tau-1)/(3\tau)
  = [[1,0],[3,1]]\cdot(\tau-1)/3`$, where $`(\tau-1)/3`$ is the same lattice as
  $`(\tau+2)/3`$, so $`1 \mapsto 2`$ and symmetrically $`2 \mapsto 1`$.

The lattice computation above is what shows, for every $`\gamma`$ at once, that this
shortcut is legitimate.

**The three local monodromies.** The loops at the cusp and at the two elliptic points
already generate all of them:

| loop | $`\gamma`$ | coordinates | slots | role |
|---|---|---|---|---|
| $`\tau \mapsto \tau+1`$ | $`[[1,1],[0,1]]`$ | $`(m+n,n)`$ | $`(0\,1\,2)`$, fixes $`\infty`$ | cusp; the twist |
| $`\tau \mapsto -1/\tau`$ | $`[[0,-1],[1,0]]`$ | $`(-n,m)`$ | $`(\infty\,0)(1\,2)`$ | $`j = 1728`$ |
| $`\tau \mapsto -1/(\tau+1)`$ | $`[[0,-1],[1,1]]`$ | $`(m-n,m)`$ | $`(\infty\,1\,0)`$, fixes $`2`$ | $`j = 0`$ |

The first is the twist of 006 §3 read on the four slots: it fixes $`\infty`$ and cycles
$`0,1,2`$. In that note's names the first two rows are $`u`$ and $`w`$.

**The catalogue.** Twelve classes of matrices give twelve permutations, and all twelve
occur:

| permutation of $`\{\infty,0,1,2\}`$ | a loop realizing it |
|---|---|
| identity | $`[[1,0],[0,1]]`$ |
| $`(0\,1\,2)`$ | $`[[1,1],[0,1]]`$ |
| $`(0\,2\,1)`$ | $`[[1,2],[0,1]]`$ |
| $`(\infty\,0)(1\,2)`$ | $`[[0,-1],[1,0]]`$ |
| $`(\infty\,1)(0\,2)`$ | $`[[1,-1],[-1,-1]]`$ |
| $`(\infty\,2)(0\,1)`$ | $`[[1,1],[1,-1]]`$ |
| $`(\infty\,0\,1)`$ | $`[[1,1],[-1,0]]`$ |
| $`(\infty\,0\,2)`$ | $`[[1,-1],[1,0]]`$ |
| $`(\infty\,1\,0)`$ | $`[[0,-1],[1,1]]`$ |
| $`(\infty\,1\,2)`$ | $`[[1,0],[1,1]]`$ |
| $`(\infty\,2\,0)`$ | $`[[0,1],[-1,1]]`$ |
| $`(\infty\,2\,1)`$ | $`[[1,0],[-1,1]]`$ |

The count is $`1 + 8 + 3`$: the identity, the eight $`3`$-cycles, and the three double
transpositions — precisely the twelve *even* permutations of the four slots. So:

- every loop is an even permutation, and no element of $`\mathrm{SL}_2(\mathbb{Z})`$
  produces an odd one;
- the loops are transitive ($`[[0,-1],[1,0]]`$ sends $`\infty`$ to $`0`$, and the powers
  of $`[[1,1],[0,1]]`$ then run through $`0,1,2`$), which is the connectedness of
  $`X_0(3)`$ over $`X(1)`$; the cusp loop alone fixes $`\infty`$, so one local monodromy
  is not enough;
- the odd permutations are *not* loops. The one closest to hand is
  $`d = [[-1,0],[0,1]]`$, acting by $`(m,n) \mapsto (-m,n)`$, the transposition
  $`(1\,2)`$ fixing $`\infty`$ and $`0`$; it is not even an element of
  $`\mathrm{SL}_2(\mathbb{Z})`$ ($`\det d = -1`$). It is arithmetic rather than
  topological — the diamond of 006 §3 — and together with the loops it generates all
  $`24`$ permutations of the four slots; the other eleven odd permutations are its
  composites with the loops, so no loop realizes any of them.

**A remark on $`X(3)`$.** The four sheets above are the cover by *lines*: the level
datum of a point of $`X_0(3)`$ is a subgroup of order $`3`$. The finer curve $`X(3)`$,
whose level datum is a full basis of $`E[3]`$, lies above it with several sheets over
each line; a loop permutes those too, and the four-slot permutation above is the one it
induces on lines.

## 4. Links

Companion notes:

- [004 — The j-invariant](004-the-j-invariant.md) — the series `jq` and its integral $`q`$-expansion
- [006 — The modular equation](006-the-modular-equation.md) — integrality and splitting of $`\Phi_N`$, which use the quotient dictionary of §2 and the monodromy of §3
- [math/010 §3](../math/010-function-field-generation.md#3-the-modular-polynomial-and-the-roots-of-the-modular-equation) — the section this pair of notes supplements

Background:

- J. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, Springer 1994, Ch. I — complex tori, isogenies, and the $`j`$-invariant.
- F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer 2005, Ch. 1 — congruence subgroups, $`X_0(N)`$, and functions on it.
