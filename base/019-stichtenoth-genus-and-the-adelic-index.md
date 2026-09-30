# Stichtenoth's genus and the adelic index

Nineteenth of the `base/` notes. [008](008-divisors-and-pic0.md) built the
divisor vocabulary and [009](009-differentials-residues-riemann-roch.md) stated
the two dimension theorems — Riemann's inequality and Riemann–Roch — and
described how the code names them. This note opens the *proof* of those theorems
that the FLT project actually formalizes: the adelic / Stichtenoth engine that
manufactures the genus, the finiteness of the spaces, and the index formula
without any analysis and without differentials. It is the mathematics behind the
fourteen declarations listed in [PORTING-RR](../lean/topics/PORTING-RR.md) §1,
the phase-1 target of that porting document; the measurement and the choice of
this route are in
[studies/riemann-roch-strategy.md](../studies/riemann-roch-strategy.md).

The engine is worth separating from the classical theory of
[009](009-differentials-residues-riemann-roch.md) because the order of
quantifiers is reversed. Classical Riemann–Roch fixes a genus $`g`$
(e.g. as $`(\deg K + 2)/2`$ for a canonical divisor $`K`$) and proves a
dimension formula. The engine here does not assume a genus at all: it defines
the *defect* $`\deg D - \ell(D)`$, shows it is bounded above, calls one plus its
maximum $`\gamma`$, and derives the dimension formula from the bookkeeping of
the adeles. What comes out is the existence of a genus together with the index
formula and the finiteness of the adelic quotient — exactly the three outputs
that the forward cone consumes
([studies/riemann-roch-strategy.md](../studies/riemann-roch-strategy.md) §5.2),
none of which the canonical divisor alone supplies.

**A warning about the three genera.** The pin carries three numbers that are
easy to conflate, and the engine distinguishes them sharply:

* the **canonical-divisor genus** $`g = (\deg K + 2)/2`$, from
  `HasCanonicalDivisor` — the genus appearing in the classical RR predicates;
* the **cohomological genus** $`g_{\mathrm{FF}} = \dim_K H^1(\mathcal{O})`$,
  `genusFF`, defined from repartitions;
* the **Stichtenoth genus** $`\gamma = 1 + \max_D(\deg D - \ell D)`$, defined by
  maximality of the defect.

The last is a proof route to the first two: the engine produces $`\gamma`$ and
the index formula unconditionally, and the equalities $`\gamma = g`$ and
$`\gamma = g_{\mathrm{FF}}`$ are separate (small) consequences. This is why the
port cannot replace Stichtenoth by the classical genus: doing so would assume
the index formula it is meant to provide.

Math first: §§1–7 are the theory, §8 summarizes the Lean encoding and maps the
fourteen declarations to the sections. Line-number citations point at
`anthropics/fermats-last-theorem@aa2d8b3`; mathlib declarations are named at tag
**v4.33.0**. The pin citations are rendered GitHub links carrying `#L` anchors.

The plan:

1. the places, divisors, and Riemann–Roch spaces, and the two standing
   hypotheses on a curve;
2. the adeles, the diagonal, and the local computation that makes the *degree*
   into a *dimension*;
3. the index of speciality and the fundamental identity that drives everything;
4. Riemann's theorem from boundedness of $`\deg D - \ell(D)`$, and the
   `RiemannGenusReachedAt` API;
5. Stichtenoth's pole-divisor package, which produces that bound;
6. Weil differentials, $`\Omega(D)`$, and the rank-one theorem;
7. the four assemblies: adelic duality, the Weil canonical divisor, and
   regular differentials $`\cong \Omega(0)`$;
8. the Lean encoding and the fourteen-node map.

## 1. The data, and the two hypotheses

Let $`K`$ be a field and $`F/K`$ a function field in one variable. A **place**
$`v`$ of $`F/K`$ is a discrete valuation ring $`\mathcal{O}_v \subseteq F`$ with
maximal ideal $`\mathfrak{m}_v`$ (the pin's `Place`, a `ValuationSubring` with
`ne_top'` and `isPrincipalIdealRing'`;
[Def_AlgebraicCurve_DivisorClassGroup.lean, lines 22–30](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L22-L30)).
Write $`k(v) = \mathcal{O}_v/\mathfrak{m}_v`$ for the **residue field** and
$`\deg v = [k(v) : K]`$ for its degree over $`K`$; write $`\mathrm{ord}_v`$ for
the normalized order, so that $`\mathrm{ord}_v(\pi_v) = 1`$ at a uniformizer
$`\pi_v`$. A **divisor** is a finitely supported integer combination of places,
$`D = \sum_v D(v)\,v`$, and its degree is

$$\deg D = \sum_v D(v)\\,\deg v .$$

This is `Divisor.degree`, defined as the additive map sending a single place to
multiplication by $`\deg v`$
([Def_AlgebraicCurve_DivisorClassGroup.lean, lines 185–192](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L185-L192)).

The two standing hypotheses the engine uses are:

* **principal divisors have degree zero.** `HasPrincipalDivisors` says that for
  every $`f \ne 0`$ there is a divisor $`(f)`$ with $`(f)(v) = \mathrm{ord}_v f`$
  and $`\deg (f) = 0`$
  ([Def_AlgebraicCurve_DivisorClassGroup.lean, lines 217–220](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L217-L220)).
  This is the divisor form of "a function has as many zeros as poles"
  ([009 §2](009-differentials-residues-riemann-roch.md)).
* **the curve hypotheses.** `IsCurveOver K F` extends
  `HasPrincipalDivisors` with two conditions: every residue field is
  finite-dimensional over $`K`$ (`finiteResidue`, so $`\deg v`$ is finite and
  positive, `one_le_deg`), and the Kähler differentials $`\Omega_{F/K}`$ are free
  of rank one over $`F`$ (`kaehler_free_rank_one`; the single dimension that
  made [009 §1](009-differentials-residues-riemann-roch.md) work)
  ([Def_AlgebraicCurve_IsCurveOver.lean, lines 15–19](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_IsCurveOver.lean#L15-L19)).

The objects of the theory are the **Riemann–Roch spaces**

$$L(D) = \\{\\, f \\in F : \\mathrm{ord}_v(f) \\ge -D(v) \\text{ for every place } v \\,\\}, \\qquad \ell(D) = \dim_K L(D),$$

`riemannRochSpace` and `LSpace`/`ell`
([Def_AlgebraicCurve_Repartitions.lean, lines 105–117](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Repartitions.lean#L105-L117),
[Def_AlgebraicCurve_AdelicIndex.lean, lines 14–16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L14-L16)).
The condition "$`\mathrm{ord}_v(f) \ge -D(v)`$" is the statement that $`f`$ has
poles no worse than $`D`$ at $`v`$, i.e. that $`f`$ lies in the space attached
to the pole bound $`D`$. The pin's order has $`\mathrm{ord}_v(0) = 0`$, and
membership is spelled with the explicit disjunct $`f = 0`$, so nothing has to be
said about $`\pm\infty`$.

**The elementary bounds.** Two facts about $`\ell`$ are used throughout and are
worth recording before the adeles. First, one point at a time:

$$\ell(D) \le \ell(D - P) + \deg P .$$

This is `ell_le_ell_sub_single_add_deg`
([S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean, line 146](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L146)).
Its proof is the prototype of every local count in this note: choose a
uniformizer $`\pi`$ at $`P`$, map $`L(D)`$ to the residue field by
$`f \mapsto \pi^{D(P)} f \bmod \pi`$, and observe that the kernel is exactly
$`L(D-P)`$. The image is a $`K`$-subspace of $`k(P)`$, so the quotient has
dimension at most $`\deg P`$. Second, adding up the points of an effective
divisor by induction gives

$$\ell(D) \le \deg D + \ell(0) \quad (D \ge 0),$$

`ell_le_degree_add_ellZero`
([line 254](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L254)).
The **first trick** of the subject now removes the effectivity hypothesis: if
$`g \in L(D)`$ is nonzero and $`(g)`$ is its principal divisor, then
$`D + (g) \ge 0`$ and $`\deg(D + (g)) = \deg D`$ (principal divisors have degree
zero), while

$$L(D) \longrightarrow L(D + (g)), \qquad f \mapsto f/g ,$$

is a $`K`$-linear bijection (`lSpaceShiftEquiv`,
[line 302](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L302)).
Hence $`\ell(D) = \ell(D + (g))`$ and

$$\ell(D) \le \deg D + 1 \quad \text{whenever } \deg D \ge 0 \text{ and } L(0) = K .$$

That last hypothesis is **`ConstantsAreBase K F`**, i.e. $`L(0) = K`$, meaning
$`K`$ is the full field of constants; it makes $`\ell(0) = 1`$
([Def_AlgebraicCurve_AdelicIndex.lean, lines 45–51](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L45-L51)),
and `ell_le_degree_add_one` is the displayed bound
([line 336](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L336)).
In defect form, with $`d(D) := \deg D - \ell(D)`$, it reads
$`d(D) \ge -1`$: the defect is bounded *below*. Riemann's theorem is the
matching bound *above*, and it is much harder.

## 2. Adeles, and why the degree is a dimension

An **adele** is a family $`\alpha = (\alpha_v)_v`$, one element of $`F`$ for
each place, subject to a growth condition at all but finitely many places. The
pin takes the bounded-adele filtration as the primitive notion:

$$A_D = \\{\\, \alpha : \mathrm{ord}_v(\\alpha(v)) \\ge -D(v) \\text{ for every } v \\,\\}, \qquad A = \bigcup_D A_D .$$

This is `adeleBdd D` and `adeleSpace K F`, both $`K`$-submodules of the full
product $`\prod_v F`$
([Def_AlgebraicCurve_AdelicIndex.lean, lines 53–63 and 94](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L53-L63)).
The **diagonal** embeds $`F`$ in the product, and `globalSub K F` is its image
([lines 76–79 and 111](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L76-L79)).
Two identifications are immediate and load-bearing:

$$A_D \cap F = L(D), \qquad A_{D_0} \subseteq A_D \text{ if } D_0 \le D .$$

The first is `map_diagonal_lSpace` / `diagonal_mem_adeleBdd_iff`
([lines 88–90 and 116–125](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L88-L90)):
an element of $`F`$ is bounded by $`D`$ at every place precisely when it lies in
$`L(D)`$; in particular $`L(D)`$ is exactly the "principal part" of $`A_D`$.

**The local dimension computation.** Fix a place $`P`$ and a uniformizer
$`\pi`$ at $`P`$. The map

$$A_D \longrightarrow k(P), \qquad \alpha \longmapsto \pi^{D(P)}\\,\\alpha(P) \bmod \mathfrak{m}_P ,$$

is $`K`$-linear and surjective, and its kernel is exactly $`A_{D-P}`$ (as a
subspace of $`A_D`$). Hence

$$A_D / A_{D-P} \\;\\cong\\; k(P), \qquad \dim_K A_D/A_{D-P} = \deg P .$$

This is `adeleBddQuotSingleEquivResidueField`
([line 449](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L449)).
Surjectivity is the only step with content, and it is short: a residue class
$`c`$ lifts to the adele supported at $`P`$ with value
$`\tilde c\,\pi^{-D(P)}`$; the kernel computation is the displayed
$`\mathrm{ord}_P`$ bookkeeping. Peeling off the points of the support of
$`D_2 - D_1`$ by induction gives the global statement

$$\dim_K A_{D_2}/A_{D_1} = \deg D_2 - \deg D_1 \quad (D_1 \le D_2),$$

`finrank_adeleBdd_quotient`
([line 583](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L583)).

This is the conceptual heart of the adelic route: **the degree of a divisor is
the dimension growth rate of the bounded adeles.** A bound on poles buys a
finite-dimensional quotient $`A_D/A_{D_0}`$, one residue field at a time, and
$`\deg`$ measures how much it buys. Every dimension count below is a comparison
of $`\deg`$ with $`\ell`$, mediated by this computation.

## 3. The index of speciality and the fundamental identity

The **index of speciality** of $`D`$ is the dimension of the adeles modulo the
bounded adeles *and* the principal adeles:

$$i(D) = \dim_K \bigl( A / (A_D + F) \bigr).$$

This is `indexOfSpecialty`, the adelic index
([Def_AlgebraicCurve_AdelicIndex.lean, lines 136–140](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L136-L140)).
It is *not* by definition $`\ell(K-D)`$; that identification is a theorem
(§6), and proving it is one of the engine's outputs. At this point it is only a
quotient of a $`K`$-vector space, possibly infinite-dimensional.

The engine's central identity compares the defect with the drop in the index.
For $`D_0 \le D`$,

$$d(D) - d(D_0) = i(D_0) - i(D), \qquad d(D) := \deg D - \ell(D).$$

This is `indexOfSpecialty_sub_of_ge`
([S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean, line 1393](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1393)),
and its dimension input is `finrank_adeleBddSup_quotient`
([line 874](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L874)). Here is the whole computation:

* $`A_D/A_{D_0}`$ has dimension $`\deg D - \deg D_0`$ (§2).
* $`A_D \cap (A_{D_0}+F) = A_{D_0} + (A_D \cap F) = A_{D_0} + L(D)`$, by the
  modular identity for the nested subspaces
  $`A_{D_0} \le A_D`$ (`adeleBdd_inf_sup_globalSub`).
* Therefore $`A_D/(A_{D_0}+L(D))`$ has dimension
  $`(\deg D - \deg D_0) - (\ell D - \ell D_0)`$, which is exactly
  $`d(D) - d(D_0)`$.
* By the second isomorphism theorem,
  $`(A_D + F)/(A_{D_0} + F) \cong A_D/(A_{D_0} + L(D))`$
  (`quotientInfEquivSupQuotient`).
* Finally $`i(D_0) - i(D) = \dim (A_D+F)/(A_{D_0}+F)`$, the drop in a chain of
  quotients (`finrank_quotient_chain`).

Two corollaries are used constantly. First, $`i`$ is **antitone**: if
$`D_0 \le D`$ then $`A_{D_0} + F \subseteq A_D + F`$, so $`i(D) \le i(D_0)`$.
Second, the *defect is monotone the other way*. Since $`L(D) \subseteq L(E)`$
for $`D \le E`$ and the quotient $`L(E)/L(D)`$ embeds in $`A_E/A_D`$,

$$\ell(E) - \ell(D) \le \deg E - \deg D, \qquad \text{i.e.} \qquad d(D) \le d(E) \quad (D \le E),$$

`ell_sub_ell_le_degree_sub_degree`
([line 686](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L686)).
So along the divisor order, $`d`$ increases by exactly the amount $`i`$
decreases.

**The two adele models, and $`H^1`$.** The pin also has a second, equivalent
model: the **repartitions** $`R`$, the $`F`$-subalgebra of $`\prod_v F`$
generated by the families that are integral at all but finitely many places
(`repartitions`,
[Def_AlgebraicCurve_Repartitions.lean, lines 51–53](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Repartitions.lean#L51-L53)).
For a curve the two agree: $`A = R`$ as $`K`$-vector spaces, $`A_D`$ matches
`repartitionsOf D`, and $`F`$ matches `principalRepartitions`. Hence

$$i(D) = \dim_K H^1(D), \qquad H^1(D) := R / (R_D + F), \qquad g_{\mathrm{FF}} := \dim_K H^1(0),$$

which is `indexOfSpecialty_eq_finrank_H1` and `genusFF`
([S_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1.lean, line 107](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1.lean#L107),
[Def_AlgebraicCurve_Repartitions.lean, lines 140–145](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Repartitions.lean#L140-L145)).
The point of the identification is that the **cohomological genus is $`i(0)`$**,
so the engine's $`\gamma`$ will be comparable to $`g_{\mathrm{FF}}`$ without any
differential theory.

## 4. Riemann's theorem from a bound on $`\deg D - \ell(D)`$

Everything now rests on one numerical statement:

$$\textbf{boundedness:} \qquad \exists b \in \mathbb{Z},\ \forall D,\quad d(D) \le b ,$$

the pin's `RiemannGenusBounded`
([Def_AlgebraicCurve_AdelicIndex.lean, lines 425–426](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L425-L426)).
Two of the fourteen declarations are about moving between this bound and
finiteness of the index, and one produces the bound.

**(a) Finite index at one divisor bounds the defect everywhere.** Suppose
$`i(D_0) \lt \infty`$ (the pin's `IndexOfSpecialtyFinite`). The fundamental
identity gives, for $`D \ge D_0`$,

$$d(D) = d(D_0) + i(D_0) - i(D) \le d(D_0) + i(D_0),$$

because $`i(D) \ge 0`$. For an arbitrary $`D`$, monotonicity gives
$`d(D) \le d(D \sqcup D_0)`$ and $`D_0 \le D \sqcup D_0`$, so the same bound
applies. Thus `IndexOfSpecialtyFinite` implies `RiemannGenusBounded`:

$$\exists b,\ \forall D,\ d(D) \le b, \qquad b := d(D_0) + i(D_0).$$

This is `degreeSub_ell_le_of_indexFinite` and
`riemannGenusBounded_of_indexFinite`
([S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean, lines 1444 and 1463](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1444-L1463)).

**(b) Boundedness produces a genus and a witness.** If $`d`$ is bounded above,
then the set of values $`\{d(D)\}`$ has a greatest element, because it is a
nonempty set of integers bounded above (`Int.exists_greatest_of_bdd`; it is
nonempty since $`d(0)`$ is a value). Put

$$\gamma := 1 + \max_D d(D), \qquad D_0 \text{ a divisor attaining the maximum.}$$

Then the three facts `RiemannGenusReachedAt γ D₀` asserts are exactly

* $`L(D_0)`$ is finite-dimensional,
* $`d(D_0) = \gamma - 1`$,
* $`d(D) \le \gamma - 1`$ for all $`D`$,

the pin's structure
([Def_AlgebraicCurve_AdelicIndex.lean, lines 406–409](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L406-L409)).
This is `exists_riemannGenusReachedAt_of_bounded`
([line 1366](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1366));
the finiteness of $`L(D_0)`$ comes from `finiteDimensional_lSpace`
([line 805](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L805)),
which derives $`\dim_K L(D) \lt \infty`$ for every $`D`$ from
$`\dim_K L(0) \lt \infty`$ and the finite-dimensionality of
$`A_{D \sqcup 0}/A_0`$.

**(c) Riemann's inequality, and equality on the upper set.** From
$`d(D) \le \gamma - 1`$,

$$\ell(D) \ge \deg D + 1 - \gamma \qquad \text{for every } D,$$

and the bound is attained at $`D_0`$. Moreover $`d`$ is *constant* from
$`D_0`$ upward: for $`D_0 \le D`$, monotonicity gives
$`d(D_0) \le d(D) \le \gamma - 1 = d(D_0)`$, hence

$$D_0 \le D \implies d(D) = \gamma - 1 .$$

That is `RiemannGenusReachedAt.eq_of_ge`
([line 982](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L982)).

**(d) The index formula, and the collapse of the adeles.** With (a)–(c), the
fundamental identity evaluated at $`D`$ and $`D \sqcup D_0`$ gives
$`i(D \sqcup D_0) = 0`$, and then

$$i(D) = d(D \sqcup D_0) - d(D) + i(D \sqcup D_0) = (\gamma - 1) - (\deg D - \ell D) = \ell(D) - (\deg D + 1 - \gamma).$$

So the index formula — the pin's `RiemannIndexFormula` — holds for **all**
$`D`$ once a genus is reached. The finiteness of the quotient comes for free in
the same breath: `adeleSpace_eq_of_genusReached` shows

$$A = A_{D_0} + F ,$$

because once $`d`$ has stabilized the bounded adeles satisfy
$`A_{D \sqcup D_0} \subseteq A_{D_0} + F`$ for every $`D`$ (this is
`adeleBddSup_eq_of_degree_sub_ell_eq`, the dimension-$`0`$ case of the
fundamental computation). Hence
$`A/(A_D+F)`$ is a quotient of the finite-dimensional
$`(A_{D_0}+F)/(A_D+F)`$, and

$$i(D) \lt \infty, \qquad i(D_0) = 0 .$$

These are `indexOfSpecialty_eq_of_genusReached` and
`indexOfSpecialty_eq_zero_of_genusReached`
([lines 1014 and 1026](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1014-L1026)).
The first is the packaged engine
$`\exists \gamma,\ \forall D,\ \text{finite} \wedge i(D) = \ell D - (\deg D + 1 - \gamma)`$
that node 3 exports, and the second says the witness $`D_0`$ is a divisor of
vanishing index — an "$`H^1 = 0`$" divisor.

**(e) The equivalence.** The converses combine into a clean dichotomy:
finiteness of the index at *one* divisor, boundedness of the defect, and
existence of a Stichtenoth genus are all the same thing. Indeed, from a reached
genus, $`A = A_{D_0}+F`$ gives `IndexOfSpecialtyFinite` at $`D_0`$
(`indexOfSpecialtyFinite_of_stichtenothGenusExists`,
[line 1478](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1478)),
and (a) supplies the reverse:

$$\texttt{StichtenothGenusExists} \iff \texttt{IndexOfSpecialtyFinite}$$

(`stichtenothGenusExists_iff_indexFinite`,
[line 1492](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1492)).
The content is that a single finite-dimensional $`H^1`$ forces global
boundedness of $`\deg - \ell`$, and a single maximal divisor of vanishing
$`H^1`$ represents the whole adele space.

**(f) A one-point witness.** The witness can be chosen supported at a single
place. `exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached` shows
that for any place $`Q`$ there is $`n`$ with $`i(nQ) = 0`$
([S_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached.lean, line 15](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached.lean#L15)),
by a short contradiction: if $`i(nQ) \ne 0`$ then $`\Omega(nQ) \ne 0`$, and
pairing a nonzero element of $`\Omega(nQ)`$ against $`L(nQ)`$ embeds $`L(nQ)`$
in $`\Omega(0)`$, so

$$\ell(nQ) \le i(0);$$

but $`d(nQ) \le \gamma - 1`$ gives $`\ell(nQ) \ge n\deg Q - (\gamma - 1)`$,
which exceeds $`i(0)`$ for $`n`$ larger than $`|i(0) + \gamma - 1|`$. Then
$`d(nQ) = \gamma - 1`$ by the fundamental identity, and
`exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists` repackages
$`nQ`$ as a witness
([line 17](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists.lean#L17)).

## 5. Producing the bound: Stichtenoth's pole-divisor package

It remains to find a curve where the defect is bounded, and this is the one
genuinely new piece of mathematics in the engine. The input is a **transcendence
tower**: a field $`E`$ with $`K \subseteq E \subseteq F`$, an element $`x \in E`$
transcendental over $`K`$, and a place $`v`$ of $`E/K`$ of degree one at which
$`x`$ has a simple pole and away from which $`x`$ is regular:

$$\mathrm{ord}_v(x) = -1, \qquad \mathrm{ord}_u(x) \ge 0 \quad (u \ne v).$$

Together with the $`K`$-linear independence of $`1, x, x^2, \dots`$ this is the
`TranscendenceTower` structure
([Def_AlgebraicCurve_PoleDivisorPackage.lean, lines 41–54](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PoleDivisorPackage.lean#L41-L54)).
The archetype is $`E = K(X)`$ with $`x = X`$ and $`v`$ the place at infinity;
$`F`$ is then a finite separable extension of $`E`$.

Push $`v`$ up to $`F`$. The **pole divisor** of $`x`$ is

$$B := \mathrm{pullback}_F([v]) = \sum_{w \mid v} e(w/v)\\,w ,$$

`TranscendenceTower.poleDivisor`
([line 62](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PoleDivisorPackage.lean#L62)).
It is effective, $`x \in L(B)`$, and by the fundamental identity for the fibre
of $`v`$,

$$\deg B = \sum_{w \mid v} e(w/v) f(w/v) = [F : E],$$

the two facts `poleDivisor_nonneg`/`xF_mem_lSpace_poleDivisor` and
`degree_poleDivisor_eq_finrank`
([line 1852](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1852)).

The second input is an **integral basis in the $`L`$-spaces**: a
$`E`$-basis $`u_1, \dots, u_n`$ of $`F`$ ($`n = [F:E]`$), all of whose
elements are regular away from $`v`$, and hence lie in $`L(cB)`$ for some
$`c \ge 0`$ (`IntegralBasisInLSpace`,
[Def_AlgebraicCurve_PoleDivisorPackage.lean, lines 70–79](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PoleDivisorPackage.lean#L70-L79)).
Such a basis exists because $`E`$ is the fraction field of a subring regular
outside $`v`$ (for $`E = K(X)`$, the ring $`K[X]`$), and an integral basis of
the integral closure is regular outside $`v`$; the regularity bounds the poles
along the fibre of $`v`$ by a single constant $`c`$.

The package is now:

$$B \ge 0, \quad \deg B = n \gt 0, \quad x \in L(B), \quad u_i \in L(cB), \quad \\{x^j u_i\\} \text{ is } K\text{-linearly independent}.$$

This is `PoleDivisorPackage`
([Def_AlgebraicCurve_PoleDivisorPackage.lean, lines 11–33](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PoleDivisorPackage.lean#L11-L33)),
assembled from a transcendence tower by
`PoleDivisorPackage.ofTranscendenceTower`
([line 1945](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1945)).
The independence is the one place where the tower hypothesis is used: it is the
statement that if $`\sum_{j,i} a_{ji} x^j u_i = 0`$ with
$`a_{ji} \in K`$, then grouping by powers of $`x`$ and using the
$`E`$-independence of the $`u_i`$ leaves a polynomial in $`x`$ with
$`E`$-coefficients that vanishes, so its coefficients vanish because $`x`$ is
transcendental (`linearIndependent_pow_mul`,
[line 1933](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1933)).

**The dimension lower bound.** For $`m \ge c`$, the elements
$`x^j u_i`$ with $`0 \le j \le m-c`$ and $`1 \le i \le n`$ all lie in
$`L(mB)`$ (since $`x^j u_i \in L((j+c)B) \subseteq L(mB)`$) and are
$`K`$-linearly independent. Counting them,

$$\ell(mB) \ge n\\,(m - c + 1), \qquad \text{hence} \qquad d(mB) = \deg(mB) - \ell(mB) \le mn - n(m-c+1) = n(c-1).$$

These are `ell_nsmul_poleDivisor_ge` and `degree_nsmul_sub_ell_le`
([lines 1587 and 1619](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1587-L1619)).
The point is that the right-hand side is independent of $`m`$: the defect stays
bounded along the ray $`m \mapsto mB`$.

**Reduction to an arbitrary divisor.** Given any $`D`$, replace it by the
effective $`D' := D \sqcup 0`$ (monotonicity, $`d(D) \le d(D')`$), and take
$`m := c + \deg D'`$. By the lower bound,
$`\ell(mB) \ge n(\deg D' + 1) \gt \deg D'`$. The inequality
$`\ell(mB) - \ell(mB - D') \le \deg D'`$ (the quotient bound of §3) then forces
$`L(mB - D') \ne 0`$: pick nonzero $`z`$ there. The membership means

$$D' \le mB + (z) ,$$

and shifting by the principal divisor $`(z)`$ preserves both the degree
($`\deg(z) = 0`$) and $`\ell`$ (§1), while the defect is monotone in the
divisor. Therefore

$$d(D) \le d(D') \le d(mB + (z)) = d(mB) \le n(c-1),$$

so the defect is bounded by $`n(c-1)`$, hence a genus
$`\gamma = n(c-1) + 1`$ is reached. This is
`degree_sub_ell_le` and `riemannGenusBounded_of_poleDivisorPackage`
([lines 1661 and 1715](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1661-L1715)).

This is Stichtenoth's proof. It is pure algebra: a transcendence basis, a
separable extension, an integral basis, and the pole divisor of the separating
element. No differentials, no residues, no topology.

**From the tower to the theorem.** For $`E = K(X)`$, $`x = X`$, and $`v`$ the
place at infinity, the tower exists (`transcendenceTower`,
[line 2361](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L2361)),
and `stichtenothGenusExists_of_ratFunc_tower` concludes
`StichtenothGenusExists` for any $`F`$ finite separable over $`K(X)`$ with
`IsCurveOver`, `Nonempty (Place K F)`, and $`L(0)`$ finite-dimensional
([line 2424](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L2424)).
Two wrappers complete the story:

* `finiteDimensional_lSpace_zero_of_constantsAreBase` reduces $`\dim_K L(0) \lt \infty`$
  to `ConstantsAreBase`, where $`L(0) = K`$
  ([line 2496](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L2496));
* a perfect field and an essentially finite-type extension give a separating
  transcendental $`t`$ with $`F/K(t)`$ finite separable
  (`IsCurveOver.exists_separating_transcendental`,
  [Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean, line 12](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean#L12)),
  which transports the $`K(X)`$ tower to $`K(t)`$ and yields the curve-level
  wrapper `exists_genus_riemannIndex_of_isCurveOver`
  ([S_AlgebraicCurve_exists_genus_riemannIndex_of_isCurveOver.lean, line 25](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_exists_genus_riemannIndex_of_isCurveOver.lean#L25)).

The headline `RationalFunctionField.stichtenothGenusExists` is exactly this,
with all the tower hypotheses as binders
([Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean, line 17](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L17)).

## 6. Weil differentials and the canonical divisor

The index formula is the analytic Riemann–Roch formula in disguise, and the
disguise is removed by taking duals. The **$`D`$-th space of Weil
differentials** is the annihilator of the bounded-plus-principal adeles:

$$\Omega(D) = (A_D + F)^{\perp} \subseteq A^{\ast}, \qquad A^{\ast} = \mathrm{Hom}_K(A, K),$$

`omegaSpace`
([Def_AlgebraicCurve_AdelicIndex.lean, lines 160–161](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L160-L161)).
By the duality between a quotient and its annihilator,

$$\dim_K \Omega(D) = i(D),$$

`finrank_omegaSpace_eq_indexOfSpecialty`
([line 182](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L182)),
and $`\Omega(D)`$ is antitone in $`D`$. The union
$`\Omega := \bigcup_D \Omega(D)`$ is `weilDifferentialModule`
([line 189](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L189)).

Multiplication of adeles by $`f \in F`$ makes $`A^{\ast}`$ an $`F`$-module:
$`(f \cdot \varphi)(\alpha) = \varphi(f\alpha)`$ (`weilSmul`,
[line 261](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L261)),
and it moves the filtration correctly:
$`f \cdot \varphi \in \Omega(D + (f))`$ when $`\varphi \in \Omega(D)`$
(`weilSmul_mem_omegaSpace_add`,
[line 298](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L298)).

**The rank-one theorem.** The module $`\Omega`$ is one-dimensional over $`F`$:

$$\varphi, \mu \in \Omega,\ \varphi \ne 0 \implies \exists! f \in F,\ \mu = f \cdot \varphi .$$

This is `WeilDifferentialRankOne`
([line 395](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L395));
it is the function-field statement that the space of differentials is
one-dimensional, proved here adelicly. The engine derives it from the genus:
`weilDifferentialRankOne_of_genusReached`
([S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean, line 1304](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1304)).
The argument is a two-dimensional refinement of the one-point trick of §4(f).
If $`\varphi, \mu \in \Omega(W)`$ were $`F`$-independent, the **double residue
pairing**

$$L(W-D) \times L(W-D) \longrightarrow \Omega(D), \qquad (g, h) \mapsto g \cdot \varphi + h \cdot \mu ,$$

would be injective (`doubleResiduePairing_injective`,
[line 1180](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1180)),
so

$$2\\,\ell(W-D) \le i(D) .$$

But $`i`$ is *linear in the degree* with slope $`1`$ on very negative divisors:
take $`D = -nQ`$ for a place $`Q`$. Then $`\ell(D) = 0`$, so
$`i(D) = n\deg Q - 1 + \gamma`$, while Riemann's inequality gives
$`\ell(W-D) \ge \deg W + n\deg Q + 1 - \gamma`$. So $`2\ell(W-D)`$ grows with
slope $`2`$ in $`n`$ while $`i(D)`$ grows with slope $`\deg Q \ge 1`$; for $`n`$
large the left side outruns the right, a contradiction
(`exists_weilSmul_eq_of_genusReached`,
[line 1262](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1262)).
This is the same shape as §4(f) and uses both halves of the index formula:
the formula itself for $`i(D)`$ at $`D = -nQ`$ and Riemann's inequality for
$`\ell(W+nQ)`$.

**The canonical divisor.** Fix a nonzero $`\varphi \in \Omega`$. A **maximal
divisor** for $`\varphi`$ is a largest $`W`$ with $`\varphi \in \Omega(W)`$;
`HasWeilCanonicalDivisor` asserts that every nonzero $`\varphi`$ has one
([line 400](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L400)).
Existence is again a boundedness argument, and here is where the genus does the
work. Since $`i(D_0) = 0`$, the set
$`\{D : \varphi \in \Omega(D)\}`$ is bounded in degree: if
$`\deg D \ge \deg D_0 + \gamma`$, then $`\ell(D - D_0) \ge 1`$ by Riemann's
inequality, so there is a nonzero $`z \in L(D-D_0)`$ with $`D_0 \le D + (z)`$;
then $`i(D + (z)) = 0`$ while $`i(D) \ge 1`$, contradicting
$`i(D+(z)) = i(D)`$. Among the divisors with $`\varphi \in \Omega(D)`$, a
maximum-degree one is automatically maximal for the order, because joining two
such divisors keeps $`\varphi`$ in the larger $`\Omega`$ and strict inclusion of
effective divisors strictly increases degree
(`degree_lt_of_lt`, `mem_omegaSpace_sup`,
[lines 95 and 131](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_exists_weilCanonical_riemannRoch.lean#L95-L131)).
This produces the Weil canonical divisor $`W`$.

**Weil duality as an isomorphism.** For a maximal $`W`$ and the rank-one
theorem, the **residue pairing**

$$L(W-D) \longrightarrow \Omega(D), \qquad g \mapsto g \cdot \varphi ,$$

is an isomorphism: injective because $`\varphi \ne 0`$ and $`F`$ is a field
(`residuePairing_injective`,
[Def_AlgebraicCurve_AdelicIndex.lean, line 366](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L366)),
surjective by rank one and maximality
(`residuePairing_surjective_of_rankOne_max`,
[line 1317](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L1317)).
Taking dimensions,

$$i(D) = \ell(W - D) \qquad \text{for every } D ,$$

which is `indexOfSpecialty_eq_ell_sub_of_rankOne_max`
([S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.lean, line 1606](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.lean#L1606)).
This is the adelic Weil duality: it identifies the adelic index with the
dimension of a Riemann–Roch space, and it is the bridge between the engine and
the classical statements of [009 §3](009-differentials-residues-riemann-roch.md).
The name "residue pairing" is classical — in the analytic model the pairing is
$`\alpha \mapsto \sum_v \mathrm{Res}_v(g\,\varphi\,\alpha)`$ — but no residue
theorem is used to define or to prove anything here.

## 7. The assemblies

The engine's outputs are combined into the four statements the forward cone
actually consumes.

**Adelic duality from full Riemann–Roch (node 12).** Given the classical
predicate `FunctionFieldRiemannRoch` — for a canonical divisor $`K`$,

$$\ell(D) - \ell(K - D) = \deg D + 1 - g, \qquad g = \frac{\deg K + 2}{2},$$

with $`K`$ supplied by `HasCanonicalDivisor`
([Def_AlgebraicCurve_RiemannRochRows.lean, lines 44–49](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RiemannRochRows.lean#L44-L49))
— together with `StichtenothGenusExists`, one proves

$$\texttt{WeilDualityAdelic}: \qquad i(D) = \ell(K - D) .$$

`weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists`
([S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists.lean, line 14](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists.lean#L14)).
The only missing ingredient is the equality of the two genera, and it is
squeezed between two evaluations:

* $`\gamma \le g`$: apply full RR at the Stichtenoth witness $`D_0`$ and use
  $`\ell(K - D_0) \ge 0`$ together with $`d(D_0) = \gamma - 1`$;
* $`g \le \gamma`$: apply full RR at $`D_1 := K + Q`$ for a place $`Q`$; then
  $`\deg(K - D_1) \lt 0`$, so $`\ell(K - D_1) = 0`$, and the Stichtenoth
  maximality $`d(D_1) \le \gamma - 1`$ gives the other inequality.

Then $`\gamma = g`$, and comparing the index formula with full RR yields
$`i(D) = \ell(K-D)`$.

**The Weil canonical divisor (node 13).** `exists_weilCanonical_riemannRoch`
produces a divisor $`W`$ and the full formula with the **cohomological** genus:

$$\exists W,\ \forall D, \qquad \ell(D) - \ell(W-D) = \deg D + 1 - g_{\mathrm{FF}} .$$

`exists_weilCanonical_riemannRoch`
([S_AlgebraicCurve_exists_weilCanonical_riemannRoch.lean, line 146](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_exists_weilCanonical_riemannRoch.lean#L146)).
This is the pure-Stichtenoth route, with no analytic input at all. Three
identifications combine:

* $`g_{\mathrm{FF}} = i(0) = \gamma`$: the first equality is the repartition
  model of §3, the second is the index formula at $`D = 0`$ together with
  $`\ell(0) = 1`$;
* the maximal divisor $`W`$ of §6 gives $`i(D) = \ell(W-D)`$;
* the index formula gives $`i(D) = \ell(D) - (\deg D + 1 - \gamma)`$.

Eliminating $`i(D)`$ and $`\gamma`$ gives the displayed formula with
$`g_{\mathrm{FF}}`$. This is Riemann–Roch in the form the differentials layer
uses, and it also exhibits $`W`$ as a canonical divisor attached to the engine's
own genus.

**Regular differentials $`\cong \Omega(0)`$ (node 14).** The last node is the
bridge to the differentials of [009 §1](009-differentials-residues-riemann-roch.md).
The **regular differentials** are those Kähler differentials that are integral
at every place,

$$\mathrm{Reg} = \\{\\, \omega \in \Omega_{F/K} : \omega \in \mathcal{O}_v \cdot d\pi_v \text{ for every } v \\,\\},$$

i.e. $`\mathrm{div}(\omega) \ge 0`$ (`regularDifferentials`,
[Def_AlgebraicCurve_RegularDifferentials.lean, lines 26–36](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RegularDifferentials.lean#L26-L36)).
For each regular $`\omega`$ the sum of local residue terms is a $`K`$-linear
functional on the adeles, $`\alpha \mapsto \sum_v \mathrm{Res}_v(\omega\,\alpha_v)`$
(`kaehlerResidueTerm`, `weilOfKaehler`,
[Def_AlgebraicCurve_WeilOfKaehler.lean, lines 78–90](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_WeilOfKaehler.lean#L78-L90)).
Because the support of the residue term is confined to
$`\mathrm{supp}(D - \mathrm{div}\,\omega)`$ for $`\alpha \in A_D`$, the sum is
finite and $`K`$-linear in $`\alpha`$ and $`\omega`$. It vanishes on principal
adeles by the **residue theorem** (`ResidueTheorem`,
[Def_AlgebraicCurve_WeilOfKaehler.lean, lines 107–109](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_WeilOfKaehler.lean#L107-L109)),
and on $`A_0`$ when $`\omega`$ is regular. Hence

$$\mathrm{Reg} \longrightarrow \Omega(0), \qquad \omega \mapsto \mathrm{weilOfKaehler}(\omega),$$

and the node asserts it is an isomorphism
(`exists_linearEquiv_regularDifferentials_omegaSpace_zero`,
[line 227](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_exists_linearEquiv_regularDifferentials_omegaSpace_zero.lean#L227)).
Injectivity is the statement that a nonzero differential has a nonzero
Weil functional (`weilOfKaehler_ne_zero_and_maximal`). Surjectivity is rank one
again: a nonzero $`\mu \in \Omega(0)`$ is $`f \cdot \varphi_0`$ for some
$`f \in F`$ and a fixed nonzero $`\varphi_0 = \mathrm{weilOfKaehler}(\omega_0)`$;
the maximal divisor of $`f\omega_0`$ is then $`\ge 0`$, because its Weil
functional $`\mu`$ lies in $`\Omega(0)`$ and maximality forces
$`0 \le \mathrm{div}(f\omega_0)`$. So $`f\omega_0`$ is regular. This is Serre
duality at $`D = 0`$ in its
elementary form, and it is the last node of the phase-1 engine. It is
**conditional**: the pin states it with `ResidueTheorem K F` and
`HasCanonicalDivisor` as hypotheses, together with the local hypotheses
`v.DCoordGenerates` and `HasCanonicalLocalResidueKStar` that belong to the
canonical-divisor phase (phase 2 in [PORTING-RR](../lean/topics/PORTING-RR.md)
§3).

## 8. How the fourteen declarations say all this

The math of the engine is the subject of §§1–7; the port's phase-1 targets are
fourteen declarations, and they are thin wrappers around it. The map:

| declaration | mathematical content | section |
|---|---|---|
| `RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase` | $`L(0) = K \implies \dim_K L(0) \lt \infty`$ | §1, §5 |
| `RationalFunctionField.stichtenothGenusExists` | the pole-divisor package bounds the defect, through the supporting lemmas `exists_riemannGenusReachedAt_of_bounded` and `stichtenothGenusExists_of_bounded` | §5, §4(b) |
| `exists_genus_riemannIndex_of_stichtenothGenusExists` | the engine $`\exists \gamma\ \forall D`$ | §4(d) |
| `exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists` | a one-point witness $`nQ`$ | §4(f) |
| `RiemannGenusReachedAt.eq_of_ge` | $`d`$ is constant from the witness upward | §4(c) |
| `exists_genus_riemannIndex_of_isCurveOver` | curve-level wrapper via a separating transcendental | §5 |
| `weilDifferentialRankOne_of_isCurveOver` | rank-one theorem for a curve | §6 |
| `indexOfSpecialty_eq_of_genusReached` | $`i(D) = \ell D - (\deg D + 1 - \gamma)`$, all $`D`$ | §4(d) |
| `indexOfSpecialty_eq_zero_of_genusReached` | $`i(D_0) = 0`$ | §4(d) |
| `omegaSpace_finite_of_genusReached` | $`\dim_K \Omega(D) = i(D) \lt \infty`$ | §6 |
| `indexOfSpecialty_eq_finrank_H1` | the two adele models agree; $`g_{\mathrm{FF}} = i(0)`$ | §3 |
| `weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists` | $`\gamma = g`$, hence $`i(D) = \ell(K-D)`$ | §7 |
| `exists_weilCanonical_riemannRoch` | $`\exists W`$ with RR against $`g_{\mathrm{FF}}`$ | §7 |
| `exists_linearEquiv_regularDifferentials_omegaSpace_zero` | $`\mathrm{Reg} \cong \Omega(0)`$ (conditional) | §7 |

The `stichtenothGenusExists` row is the only one where a supporting pair of
lemmas sits between the public statement and the mathematics; the other
thirteen are the statements of [PORTING-RR](../lean/topics/PORTING-RR.md) §1
directly.

### The encoding

Three encoding choices carry the mathematics.

**Adeles are a submodule of a product, not a restricted product.**
`adeleSpace K F` is defined as the supremum $`\bigcup_D A_D`$ of submodules of
the full product `Place K F → F`
([Def_AlgebraicCurve_AdelicIndex.lean, line 94](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L94)).
Because each $`A_D`$ is cut out by the pointwise condition
$`v.\mathrm{adicValuation}(\alpha\,v) \le \exp(D\,v)`$ and the $`A_D`$ are
directed, the "all but finitely many places are integral" condition is encoded
as membership in one $`A_D`$, with $`D`$ the pole bound. The advantage is that
every finiteness statement becomes a statement about a *single* submodule
quotient $`A_D/A_{D_0}`$. The valuation is the `WithZero ℤᵐ⁰`-valued
`adicValuation` of the height-one spectrum, and $`\mathrm{ord}`$ is the
additive logarithm, so "bounded by $`D`$" is a clean inequality in a linear
order with zero adjoined.

**Finiteness is `Module.Finite`, dimension is `Module.finrank`, and all
dimension identities are `finrank` bookkeeping.** The engine never proves a
finite-dimensionality by hand: it uses `Submodule.finrank_quotient_add_finrank`,
`Submodule.finrank_sup_add_finrank_inf_eq`,
`LinearMap.finrank_le_finrank_of_injective`,
`LinearEquiv.finrank_eq` and `Subspace.dual_finrank_eq`. The mathematical
content is pushed into the two structure lemmas
`finrank_adeleBdd_quotient` (the degree computation) and
`finrank_adeleBddSup_quotient` (the fundamental identity), and everything else
is linear algebra over $`K`$. The one place a genuine finiteness theorem is
proved is `finiteDimensional_lSpace`, by embedding the quotient
$`L(D \sqcup 0)/L(0)`$ into the finite-dimensional `Module.Finite` quotient
$`A_{D \sqcup 0}/A_0`$

```lean
theorem finiteDimensional_lSpace [hL0 : FiniteDimensional K (LSpace (0 : Divisor K F))]
    (D : Divisor K F) : FiniteDimensional K (LSpace D)
```

([line 805](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean#L805)).

**The genus is a `Prop`-valued structure with a `ℤ` parameter, not a function.**
`RiemannGenusReachedAt γ D₀` is a structure with three fields
(`finite`, `eq`, `isMax`), and `StichtenothGenusExists` existentially
quantifies $`\gamma`$ and $`D_0`$
([Def_AlgebraicCurve_AdelicIndex.lean, lines 406–421](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L406-L421)).
This is faithful to the mathematics — $`\gamma`$ is defined *by a maximality
property*, and different witnesses can be chosen — and it is why the port can
keep the statement verbatim while changing the proof. The two other genera are
separately defined total functions (`genus`, `genusFF`), and the equalities
between them are theorems, not definitions.

### What mathlib supplies

mathlib contributes the valuation and DVR layer but none of the curve theory.
The statements the engine rests on are:

* `ValuationSubring`, `IsDiscreteValuationRing.exists_irreducible`,
  `HeightOneSpectrum` and its `valuation` for `Place`, `ord`, `adicValuation`
  and the uniformizer;
* `Submodule.dualAnnihilator`, `Submodule.dualQuotEquivDualAnnihilator`,
  `Subspace.dual_finrank_eq` for $`\Omega(D)`$ and $`\dim \Omega(D) = i(D)`$;
* `Submodule.finrank_quotient_add_finrank`,
  `Submodule.finrank_sup_add_finrank_inf_eq`,
  `LinearMap.quotientInfEquivSupQuotient`,
  `Submodule.quotientQuotientEquivQuotient` for the exact-sequence bookkeeping
  of §3;
* `Int.exists_greatest_of_bdd` for turning boundedness into a maximum;
* `Module.Finite`/`Module.finrank` and `LinearEquiv.finrank_eq` for every
  dimension count.

There is **no** `RiemannRoch`, no function-field genus and no function-field
adelic space in mathlib: `NumberTheory/NumberField/AdeleRing` and
`RingTheory/DedekindDomain/FiniteAdeleRing` are number-field only. The `LSpace`,
`ell`, `repartitions`, `adeleBdd`, `indexOfSpecialty`, `omegaSpace`, `genusFF`
and `RiemannGenusReachedAt` vocabulary is therefore bespoke, and the port is a
transcription plus elaboration rather than a search for a mathlib substitute
([PORTING-RR](../lean/topics/PORTING-RR.md) §3, where the audit is recorded).

### Dependencies and the conditional node

Among the fourteen nodes the pin's graph has the following edges:

```text
exists_genus_riemannIndex_of_isCurveOver
    -> stichtenothGenusExists, exists_genus_riemannIndex_of_stichtenothGenusExists
weilDifferentialRankOne_of_isCurveOver -> stichtenothGenusExists
weilDualityAdelic_of_...
    -> indexOfSpecialty_eq_of_genusReached
exists_riemannGenusReachedAt_nsmul_single
    -> indexOfSpecialty_eq_of_genusReached, omegaSpace_finite_of_genusReached
exists_weilCanonical_riemannRoch
    -> stichtenothGenusExists, indexOfSpecialty_eq_finrank_H1,
       indexOfSpecialty_eq_of_genusReached, weilDifferentialRankOne_of_isCurveOver
exists_linearEquiv_regularDifferentials
    -> stichtenothGenusExists, weilDifferentialRankOne_of_isCurveOver
```

The first thirteen are unconditional against the ported place/divisor
vocabulary. The fourteenth is the exception: the pin states it with
`(hRT : ResidueTheorem K F)` and `[HasCanonicalDivisor (K := K) (F := F)]` and
local residue hypotheses, so it can land in phase 1 and be fed once the
canonical-divisor and analytic blocks are ported. Nothing else in the engine
needs the residue theorem — that is the point of choosing the Stichtenoth route.

## 9. Links

* [008 — Divisors, linear equivalence, and Pic⁰](008-divisors-and-pic0.md) —
  the point/divisor vocabulary, the degree, and the genus as a fact.
* [009 — Differentials, residues, and Riemann–Roch](009-differentials-residues-riemann-roch.md)
  — the classical statements of Riemann's inequality and Riemann–Roch that the
  engine proves, and the residue theorem used by node 14.
* [015 — Places and their extensions](015-places-and-extensions.md) — the local
  theory ($`e`$, $`f`$, the fundamental identity) behind the pole divisor.
* [017 — The rational function field and principal divisors](017-rational-function-field-and-principal-divisors.md)
  — the $`K(X)`$ model and the degree-zero principal divisor used as the base
  of the transcendence tower.
* [PORTING-RR](../lean/topics/PORTING-RR.md) — the port blueprint whose phase 1
  is these fourteen nodes.
* [studies/riemann-roch-strategy.md](../studies/riemann-roch-strategy.md) — the
  measurement, the two routes, and the three genera.
* [Def_AlgebraicCurve_AdelicIndex.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean)
  and
  [Def_AlgebraicCurve_Repartitions.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Repartitions.lean)
  — the bespoke vocabulary quoted throughout.
