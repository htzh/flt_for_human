# The Riemann–Roch statement hierarchy

[009](009-differentials-residues-riemann-roch.md) gives the Riemann–Roch statement
and its consequences, and [019](019-stichtenoth-genus-and-the-adelic-index.md) the
adelic engine that produces it. This note is about something narrower and, for a
port, load-bearing: the **shape of the statements**, not the proofs. The theorem
appears at half a dozen strengths — an inequality, an index formula, three
duality forms, the identity itself — and the relations among them are a small
lattice with two directions. Along the way it pins down the object that the
symbol $`\dim`$ in the statement actually refers to, three times over, and what a
canonical divisor is when you cannot yet *choose* one.

Nothing here needs a curve that embeds anywhere, or a smooth projective model:
$`F`$ is a finitely generated field of transcendence degree one over $`K`$, and
the only geometric input is the discrete valuation attached to each place.

## 1. The cast

$`F/K`$ is a field of one variable: $`K`$ algebraically closed or not, $`F`$ a
finitely generated extension of transcendence degree one. A **place** $`v`$ is a
proper valuation subring of $`F`$ containing $`K`$; its residue field is finite
over $`K`$ in the situation we care about. Write $`\mathrm{ord}_v`$ for the
additive valuation and $`\deg v = [\kappa(v) : K]`$ for the residue degree.

A **divisor** is a finitely supported $`D \colon \mathrm{Places} \to \mathbb{Z}`$,
with $`\deg D = \sum_v D(v)\, \deg v`$ (008 §2). A function
$`f \in F^\times`$ has the principal divisor $`(f)(v) = \mathrm{ord}_v f`$, of
degree zero. Two divisors are linearly equivalent when they differ by a
principal one.

The one piece of data the statements need beyond this is a **differential**: an
element of $`\Omega[F/K]`$, the module of Kähler differentials, which is
one-dimensional over $`F`$ for a function field. Its local behaviour at $`v`$ is
recorded by $`\mathrm{ord}_v(\omega) = \mathrm{ord}_v(\omega / dt_v)`$ for a
uniformiser $`t_v`$ — the order of vanishing of the coefficient. That quantity
has the shape of a divisor.

## 2. Dimension, three times over

The word "dimension" in Riemann–Roch is doing three jobs, and the hierarchy only
makes sense once they are separated. All three are dimensions of $`K`$-vector
spaces attached to one divisor $`D`$.

### 2.1 Functions with a pole bound: $`\ell(D)`$

$$L(D) \\;=\\; \\{\\, f \in F \\;:\\; \mathrm{ord}_v(f) + D(v) \ge 0 \ \text{for every place } v \\,\\},
  \qquad \ell(D) \\;=\\; \dim_K L(D).$$

This is 009 §3's space. It is a $`K`$-subspace of the field $`F`$ cut out by
local conditions: at each place, $`f`$ may have a pole only as far as $`D`$ allows.
$`L(D)`$ is *the* object the theorem is about. That it is finite-dimensional is
not part of the definition — for a function field it is a theorem, and one the
ladder leans on, so the statements below carry the finiteness where they need it.

There is a second way to say the same thing, and it is the one the code is built
on. Let

$$A_F \\;=\\; \bigcup_{D} A_F(D), \qquad A_F(D) \\;=\\; \prod_v \\{\\, \alpha_v \in F \\;:\\; \mathrm{ord}_v(\alpha_v) \ge -D(v) \\,\\}$$

be the **bounded adeles** at $`D`$, and $`A_F`$ their union over all $`D`$ — the
**adeles**, a restricted product in which every element is bounded below at all
but finitely many places. The diagonal embedding
$`F \hookrightarrow \prod_v F`$ has image $`A^0`$, the principal adeles. Then
evaluation of the diagonal at the places is an isomorphism

$$L(D) \\;\cong\\; A_F(D) \cap A^0,$$

so that

$$\ell(D) \\;=\\; \dim_K \bigl( A_F(D) \cap A^0 \bigr).$$

Read that again, because it is the bridge the whole hierarchy crosses: $`\ell`$ is
the dimension of a *subspace of the adele space* — an intersection of a local
condition with the diagonal. Nothing about $`F`$ as an abstract field survives
except through the places.

### 2.2 The quotient: index of speciality and the genus

The complementary space is not another space of functions; it is a quotient.

$$i(D) \\;=\\; \dim_K \frac{A_F}{A_F(D) + A^0}, \qquad g_{\mathrm{FF}} \\;=\\; i(0).$$

This is the **index of speciality**. $`i(0)`$ is by definition the genus that the
adelic construction measures, and it is the genus that appears in the
cohomological form of Riemann–Roch. Two features matter for the statement
hierarchy:

- the quotient is taken *inside* the adeles, so $`i(D)`$ exists as a number the
  moment the quotient is finite-dimensional. That finiteness is a genuine
  hypothesis in the theory — it is what "the genus exists" means — and not a
  formality: for a general $`F`$ one must prove it, and that proof is where
  Stichtenoth's pole-divisor package enters (019 §5);
- $`i(D) = \dim H^1(D)`$ for the curve's coherent cohomology, i.e. $`i`$ is the
  $`H^1`$-side of the Euler characteristic. So

$$\ell(D) - i(D) \\;=\\; \chi(D) \\;=\\; \deg D + 1 - g$$

is Riemann–Roch written with the Euler characteristic in the middle — the form
the statement ladder below starts from.

### 2.3 Differentials: $`\Omega(D)`$ is the dual of the quotient

The third space is the differentials bounded by $`D`$, and it is defined by
annihilation rather than by a local condition:

$$\Omega(D) \\;=\\; \\{\\, \varphi \in A_F^{\vee} \\;:\\; \varphi \text{ vanishes on } A_F(D) + A^0 \\,\\},
  \qquad \dim_K \Omega(D) \\;=\\; i(D).$$

The equality of dimensions is not a theorem about differentials; it is the
first-isomorphism-theorem duality

$$\Omega(D) \\;\cong\\; \Bigl( \frac{A_F}{A_F(D)+A^0} \Bigr)^{\vee},$$

i.e. the annihilator of a subspace is the dual of the quotient. So **the
$`H^1`$ quotient and the space of bounded differentials are the same object seen
from two sides**, and $`i(D) = \dim \Omega(D)`$ holds with no finiteness input.

This is worth stating plainly because it removes a common confusion: in the
statement $`\ell(D) - \ell(K - D) = \deg D + 1 - g`$, the second term is *not*
the dimension of a second space of functions. It is the dimension of a space of
differentials, which is a dual of a quotient of adeles. The notation
$`\ell(K-D)`$ is a convenience: it names that dimension by the divisor it
corresponds to.

### 2.4 The pairing that identifies them, and Serre duality

Multiplication ties the two together. Fix a nonzero $`\omega \in \Omega[F/K]`$ and
let $`W = (\omega)`$ be its divisor. Multiplication by $`\omega`$ maps a function
$`g`$ with $`(g) + W - D \ge 0`$ to a differential $`g\omega`$ whose poles are
bounded by $`D`$; summing the local residues of $`g\omega`$ produces a functional
on the adeles, hence an element of $`\Omega(D)`$:

$$\mathrm{res} \colon L(W - D) \\;\longrightarrow\\; \Omega(D), \qquad
  g \\;\longmapsto\\; \bigl( \alpha \mapsto \textstyle\sum_v \mathrm{Res}_v(\alpha_v\\, g\\, \omega) \bigr).$$

**Serre duality** is the statement that this is an isomorphism. Its content is
one rank-one condition: the Weil differentials — the functionals on the adeles
that vanish on $`A^0`$ — form a one-dimensional $`F`$-space, generated by the
functional attached to $`\omega`$. Given that, $`\mathrm{res}`$ is injective
(a nonzero $`g\omega`$ pairs nontrivially with a suitable test adele, because the
trace pairing at a place is nondegenerate) and surjective (a functional of the
right shape is $`g\omega`$ for a unique $`g`$), so

$$\ell(W - D) \\;=\\; \dim_K \Omega(D) \\;=\\; i(D).$$

That identity, substituted into the Euler characteristic, *is* Riemann–Roch.
Everything in the next section is a way of saying how much of this one needs to
be assumed.

## 3. The canonical divisor

A canonical divisor is the divisor of a nonzero differential:
$`K = (\omega)`$, i.e. $`K(v) = \mathrm{ord}_v(\omega)`$. Two differentials differ
by a nonzero function, so their divisors differ by a principal divisor: the
canonical divisor is well defined up to linear equivalence, and that is all
Riemann–Roch needs, since $`\ell`$ and $`\deg`$ are insensitive to adding a
principal divisor (with $`g`$ fixed).

Two numbers follow, and they are the reason the genus is not an extra input:

- $`\deg K = 2g - 2`$: in Riemann–Roch take $`D = K`$. Then
  $`\ell(K) - \ell(0) = \deg K + 1 - g`$, and $`\ell(K) = g`$ (the canonical space),
  $`\ell(0) = 1`$ (constants), so $`g - 1 = \deg K + 1 - g`$.
- $`\ell(0) = 1`$ is the statement that the functions without poles are exactly
  the constants: $`L(0) = K`$, inside $`F`$.

The genus itself can be introduced in either of the two ways the dimensions
suggest, and the port keeps both:

$$g_{\mathrm{can}} \\;=\\; \Bigl\lfloor \frac{\deg(\omega_0) + 2}{2} \Bigr\rfloor
  \quad\text{(from a chosen differential)},\qquad
  g_{\mathrm{FF}} \\;=\\; i(0) \\;=\\; \dim H^1(0)\ \text{(from the adeles)}.$$

That these agree, $`g_{\mathrm{can}} = g_{\mathrm{FF}}`$, is a theorem, not a
definition — and a theorem with real content, since one is read off a single
divisor and the other from the whole adelic quotient. The proof uses
Riemann–Roch, the adelic duality form, and the statement that the constants are
$`K`$: the last two pin the canonical degree and the index at the canonical
divisor, and Riemann–Roch then identifies the two integers.

Two further structural facts about differentials are needed *before* any of this
can be stated honestly, and the port carries them as hypotheses precisely
because a bare function field does not have them for free:

- the differentials are one-dimensional over $`F`$
  ($`\Omega[F/K] \cong F`$ as an $`F`$-vector space) — the Kähler rank;
- a local coordinate exists at every place — a uniformiser $`t_v`$ whose
  differential generates $`\Omega`$ locally — which is what makes
  $`\mathrm{ord}_v(\omega)`$ well defined as a divisor coordinate.

## 4. The statement ladder

Now the hierarchy. Each rung is a *statement*; the arrows are implications
between them. They are all phrased for the same fixed $`K, F`$, quantified over all
divisors $`D`$ and all nonzero differentials $`\omega`$. The name in
$`\mathrm{...}`$ is the label the port gives the statement — §8 says where each
one lives — and it is worth knowing that every rung carries its own instance
arguments, so a rung is a statement about a *class* of curves rather than about
one fixed $`F/K`$.

**Rung 0 — the curve.** $`\mathrm{IsCurveOver}`$: principal divisors exist with
degree zero (so $`\deg`$ descends to classes), the residue field at every place is
finite over $`K`$, and $`\Omega`$ is free of rank one. This is the standing
hypothesis of every rung above; on its own it says nothing about $`\ell`$.

**Rung 1 — the inequality.** $`\ell(D) \ge \deg D + 1 - g`$ for all $`D`$: Riemann's
inequality. This is the half of Riemann–Roch that needs no duality — it follows
from the adelic description of $`L(D)`$ and an index count.

**Rung 2 — the index formula.**

$$i(D) \\;=\\; \ell(D) - (\deg D + 1 - g) \qquad \text{for all } D.$$

This is Riemann–Roch with $`i(D)`$ left as the quotient dimension: the honest
form, because it names what the second term is.

**Rung 3 — duality forms.** Three equivalent ways of saying that the index is a
space of differentials:

$$\text{(3a)}\quad i(D) = \ell(K - D); \qquad
  \text{(3b)}\quad \dim \Omega(D) = \ell(K - D); \qquad
  \text{(3c)}\quad \ell(D) - \ell(K - D) = \deg D + 1 - g .$$

(3a) and (3c) are rearrangements of each other given the index formula; (3b) is
the differential version, and the one Serre duality feeds.

**Rung 4 — Riemann–Roch.** $`\ell(D) - \ell(K - D) = \deg D + 1 - g`$, with a
canonical divisor *named* by a differential: $`K = (\omega)`$.

The arrows between rungs are cheap where one statement is a rearrangement of
another and expensive where a new object has to be produced:

| from | to | what the step is |
|---|---|---|
| (3c) | (3a) | rearrange using the index formula |
| (3a) + index formula | (3c) | rearrange |
| (3b) | (3a) | identify $`\dim \Omega(D)`$ with $`i(D)`$ (annihilator duality) |
| index formula | inequality | $`i(D) \ge 0`$ |
| Riemann–Roch + genus exists | (3a) | the analytic-to-arithmetic step, §5 |

Alongside the ladder sits a second, independent axis — the **existence of the
genus**, which the rungs above all presuppose in order to write $`g`$ at all:

- $`\mathrm{IndexOfSpecialtyFinite}`$: some $`D_0`$ has $`A_F / (A_F(D_0)+A^0)`$
  finite-dimensional;
- $`\mathrm{RiemannGenusBounded}`$: $`\deg D - \ell(D)`$ is bounded above;
- $`\mathrm{RiemannGenusReachedAt}(\gamma, D_0)`$: $`L(D_0)`$ finite, and
  $`\deg D - \ell(D) \le \gamma - 1`$ for all $`D`$, with equality at $`D_0`$;
- $`\mathrm{StichtenothGenusExists}`$: a place exists, $`L(0)`$ is
  finite-dimensional, and some $`D_0`$ reaches the genus.

They are four ways of saying one thing — that the genus exists — and each asks
for a *different* piece of analysis: finiteness of a quotient, boundedness of a
numerical function, attainment of a supremum, and a package that also supplies a
place to start from. The port proves the equivalence
$`\mathrm{StichtenothGenusExists} \leftrightarrow \mathrm{IndexOfSpecialtyFinite}`$
(one direction is a finiteness transfer through the adele filtration, the other
constructs the witness), and derives
$`\mathrm{RiemannGenusBounded}`$ from the genus together with the constants
statement, by way of a pole-divisor package: a bound on $`\deg D - \ell(D)`$ for
large $`D`$ requires knowing that a divisor with sufficiently negative part has no
functions and that adding places raises the count predictably.

## 5. The two directions

The ladder has arrows in both directions between its analytic bottom and its
arithmetic top, and they are genuinely different theorems.

**Analysis to algebra.** Assume the residue theorem (below) and the curve axioms.
The step that matters is the production of a *maximal* functional: the residue
theorem yields a nonzero linear functional on the adeles that lies in
$`\Omega((\omega))`$ and whose pole divisor is maximal among those containing it.
Maximality is exactly what makes the residue pairing
$`L((\omega) - D) \to \Omega(D)`$ bijective for every $`D`$ — injective because a
nonzero function has a zero or a pole somewhere and the pairing sees it, surjective
because a functional with a larger pole divisor than allowed would contradict
maximality — so

$$\dim \Omega(D) \\;=\\; \ell((\omega) - D),$$

and the index formula follows by annihilator duality. That is the whole analytic
content of the ladder: everything else is rearrangement.

The residue theorem here is the statement that for $`f \in F`$ and
$`\omega \ne 0`$,

$$\sum_v \mathrm{Res}_v(f\omega) \\;=\\; 0,$$

the sum of local residues of a global differential over all places. It is the one
analytic input; everything else on the ladder is algebra. Two models of the
residue map appear in the port, and the difference between them is exactly the
strength of the hypothesis:

- the abstract $`\mathrm{ResidueTheorem}`$, whose residue is read off the
  Kähler differential and a trace on the residue field;
- the $`\mathrm{ResidueTheoremK}`$, which fixes a *family of local residue data*
  $`R_{\mathrm{fam}}`$ at every place (a canonical choice, supplied
  unconditionally by the port's local-residue instance) and states the same
  vanishing for the functional built from it.

The second is what the port proves over an algebraically closed constant field:
first for the rational function field $`K(T)`$, where every residue is explicit,
then for a general $`F`$ by the cotrace descent that compares the residue of
$`F`$ with the residue of $`K(T)`$ along a separating transcendental.

**Algebra to analysis.** In the other direction, Riemann–Roch plus the existence
of the genus gives back the duality statement: from the index formula and the
canonical divisor one shows $`i(D) = \ell(K-D)`$ for a canonical divisor, which is
the adelic duality rung. This direction is where the genus-existence axis is
spent; without $`g`$ there is nothing to compare $`\deg D - \ell(D)`$ against.

So the ladder is not a chain: the analytic statements imply the algebraic ones,
the algebraic statements imply the duality rung, and the genus-existence axis is
used by both. The port's route diagram, in the small:

```
  ResidueTheoremK  (the K model: a local residue family at every place)
        │  cotrace descent, plus the explicit computation on K(X)
        ▼
  ResidueTheorem  (Σ_v Res_v(fω) = 0)
        │  + the curve axioms
        ▼
  a maximal functional in Ω((ω))  ──►  dim Ω(D) = ℓ((ω) − D)
        │                                     │  annihilator duality
        ▼                                     ▼
  index formula  i(D) = ℓ(D) − (deg D + 1 − g)  ──►  Riemann–Roch
        ▲
        │  + the genus exists, and the constants are K
        └────  duality rung  i(D) = ℓ(K − D)
```

## 6. The wrapper stack

For application the interesting question is not which rung is true but **how few
hypotheses** the top of the ladder can be stated under. Four wrappers, each
strictly weaker in hypotheses than the one below it, carry the statement from the
curve package down to a bare transcendental generator. Reading them in order says
what each layer of structure is worth.

1. **Riemann–Roch from the K residue theorem.** Hypotheses: the curve axioms,
   the canonical divisor, generation of $`\Omega`$ at every place, $`F`$ finite and
   separable over a rational function subfield $`K(t)`$ (with the $`K`$-algebra
   structure transported along that identification), and $`\mathrm{ResidueTheoremK}`$.
   Nothing is derived here; this is the assembled statement.
2. **Riemann–Roch over an algebraically closed field.** The residue theorem is
   supplied rather than assumed: over algebraically closed $`K`$ the K model is
   proved, so the hypothesis list loses it and keeps only the curve package.
3. **Riemann–Roch from the curve over an algebraically closed field.** All three
   residue-side hypotheses disappear — a local residue at every place, a canonical
   residue *family* compatible with the trace, and separability of each residue
   extension. The first two are supplied unconditionally by the port's local
   residue instance, and the third follows from perfectness together with the
   curve axioms, since residue extensions of a curve over a perfect field are
   separable.
4. **Riemann–Roch from a transcendental generator.** Hypotheses: $`K`$
   algebraically closed, $`x \in F`$ transcendental over $`K`$, and $`F`$ finite
   over $`K(x)`$. Everything else is derived: a separating transcendental $`t`$
   (perfectness allows replacing $`x`$), then the curve axioms, the canonical
   divisor, generation of $`\Omega`$, and the whole tower of instances over a
   rational function field — transporting $`F`$ along $`K(x) \cong K(t)`$ is what
   turns "finite over $`K(x)`$" into the tower hypothesis the previous rung wants.

The direction of travel is the one that matters mathematically: the *content* of
Riemann–Roch is unchanged across the four, but the amount of structure the
statement has to be handed grows as the hypotheses shrink. Layer 4 is the form in
which the theorem is actually consumed: every application in the FLT development
has a specific transcendental in hand ($`j`$, $`j_{q}`$, the uniformising
coordinate of $`X_0(N)`$) and no desire to verify a curve package by hand.

## 7. What is independent of what

The hierarchy is a lattice rather than a chain because four of its inputs are
independent of the rest and of each other:

- **the canonical divisor exists** — a divisor realising $`\mathrm{ord}_v(\omega)`$
  for every $`\omega`$, with the bound attained. This is a finiteness statement,
  not a tautology: $`\mathrm{ord}_v(\omega)`$ must vanish at all but finitely many
  places and the resulting function on places must be the one that is *maximal*
  among those bounding $`\omega`$. It is proved for a curve over a perfect field
  from the Kähler rank and the separating-transcendental machinery.
- **the genus exists** — the adelic finiteness axis of §4. Also not automatic,
  and provable in several ways (Stichtenoth's pole-divisor package, or the index
  formula itself once duality is known).
- **the constants are the base field** — $`\ell(0) = 1`$. It is needed both to
  identify $`g_{\mathrm{can}}`$ and $`g_{\mathrm{FF}}`$ and to
  make $`\deg K = 2g - 2`$ come out, and it is a genuinely separate input: a
  function field with a larger constant field has $`\ell(0) \gt 1`$.
- **generation of $`\Omega`$ at each place** — the local coordinate exists. This
  one is *local* and per-place, and it is the hypothesis that makes the
  divisor-valued $`\mathrm{ord}_v(\omega)`$ meaningful.

Each of the four is proved unconditionally in the port's setting (curve over a
perfect field, essentially of finite type), which is why the top of the stack can
be reached at all; but the statements are organised so that they are visibly
separate, and so that a route that supplies one of them differently (a different
genus construction, a different residue theorem) plugs in at one place.

## 8. Lean: where the hierarchy lives

The statements of §4 are the port's `Defs/RiemannRochRows.lean` (the `Prop` rows
and their two cheap implications), `Defs/AdelicIndex.lean` (the dimensions, the
genus axis, the annihilator duality), `Defs/CanonicalDivisor.lean` (the canonical
divisor, `genus`, `LSpace`/`ell`) and `Defs/Repartitions.lean` (adeles, `H1`,
`genusFF`). The arrows of §5 are in `RiemannRoch/Assembly.lean` (the analytic
assemblies), `Genus/Index.lean` and `Genus/Stichtenoth.lean` (the genus axis), and
`ResidueTheorem/{KRatFunc,KFamily,KCotrace,GeneralFromK}.lean` (the residue
theorem and its descent). The wrapper stack of §6 is `ResidueTheorem/RRAssembly.lean`,
with `IsCurveOver/{Transcendental,EssFiniteType,PerfectField}.lean` supplying the
derivations the bottom wrapper needs.

Each of those modules is wired to the pin's statements by `spec-pin:` lines and
checked declaration by declaration: `RRAssembly` 41 statements, `Core` 42,
`Calculus` 32, `DivPow` 51, `RatFunc` 7, `KCotrace` 42, `KFamily` 29,
`CompletionTraceCommute` 2 — `0 mismatch, 0 missing` throughout, and the four
headline wrappers of §6 carry exactly the axioms `[propext, Classical.choice,
Quot.sound]`.

Two conventions of the port worth knowing when reading the names:

- the pin tags its generated declarations with the section they came from
  (`p0n25_wkc_…`); the port drops that label, so a name like
  `wkc_weilOfKaehlerK_single` is the pin's `p0n25_wkc_weilOfKaehlerK_single`.
  The checker strips the label on the pin side, so the rename needs no
  per-declaration bookkeeping;
- the `Prop`-valued rows (`FunctionFieldRiemannRoch`, `WeilDuality`, …) all
  quantify their instance arguments — the curve axioms, the canonical divisor,
  the per-place generation — so the *rung* is a statement about a class of
  curves, while the wrapper stack of §6 is the statement about a *given*
  $`F/K`$ with those instances discharged.

## 9. Links

- [008 — Divisors and Pic⁰](008-divisors-and-pic0.md): divisors, degree, linear
  equivalence, and the Jacobian.
- [009 — Differentials, residues, and Riemann–Roch](009-differentials-residues-riemann-roch.md):
  the statement, its consequences, and the genus computations.
- [019 — Stichtenoth's genus and the adelic index](019-stichtenoth-genus-and-the-adelic-index.md):
  the adelic engine that produces the genus and the index formula.
- [015 — Places and extensions](015-places-and-extensions.md): residue degrees and
  ramification, the local data behind $`\deg`$.
- [017 — The rational function field](017-rational-function-field-and-principal-divisors.md):
  the $`\mathbb{P}^1`$ base case, where every residue is explicit.
