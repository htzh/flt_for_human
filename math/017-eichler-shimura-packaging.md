# The Eichler–Shimura cohomology packaging: the 33-node layer the relaxed route removes

**Status.** Mathematical exposition and a porting judgment, pinned to the FLT pin
`aa2d8b3`. Companion to
[015-weight-two-hecke-periods.md](015-weight-two-hecke-periods.md) (route B, the
weight-2 period map) and
[016-mod-p-weight-filtration.md](016-mod-p-weight-filtration.md) (the gap). The
measurements are the relaxed route's removed set `R` of
[../studies/eichler-shimura-bypass-scout.md](../studies/eichler-shimura-bypass-scout.md)
§6: **33 nodes / 10,789 `S_` lines** in the `HeckeEis` namespace, the
**cohomological packaging** of the Eichler–Shimura map (scout §0).

## 0. The question

The relaxed route keeps route B, the 12-node elementary primitive and C′, and
drops these 33 nodes. Route B is accessible: a single 4,308-line file, graph
closure 1, no cohomology quotient, no dimension theory. The question this note
answers is whether the 33-node packaging is *mathematically interesting and
graspable* enough that keeping it — porting the classical Eichler–Shimura story
instead of bypassing it — is the better route, despite costing more.

**Short answer.** The packaging is the *explanatory* mathematics and route B is
the *degenerate* one: route B is the $`n = 0`$ slice where the cohomology
quotient and the anti-holomorphic half both vanish, so it is clean but it does
not show what the Eichler–Shimura map actually is. The packaging is the classical
theorem and it is not hard to grasp at the level of ideas. But the 33 nodes are
dominated by three things route B deliberately avoids — the parabolic quotient,
the conjugate-linear involution, and the integral-basis/dimension machinery — and
of these only the dimension theory is geometry the endgame needs anyway. So the
packaging **clarifies the mathematics and muddles the port**. §5 gives the staged
recommendation.

## 1. The 33 nodes by role

Everything lives in the pin's `HeckeEis` namespace, over
$`\Gamma = \Gamma_0(N)`$, $`V_n = \mathrm{Sym}^n`$ realized as degree-$`n`$
binary forms (`BinaryForm ℂ n`), with representation $`\rho_n =`$
`binaryFormRepSL` and Hecke endomorphism $`a_\ell =`$ `binaryFormAlphaAdj`. The
weight is $`k = n+2`$.

| group | nodes | lines | content |
|---|---:|---:|---|
| 1. the period map | 4 | 394 | `eichlerShimuraMap` is additive, ℂ-homogeneous, injective |
| 2. the two halves | 5 | 2,000 | conjugate-linear involution, complementarity, packaged isomorphism |
| 3. Hecke equivariance | 4 | 1,742 | existence of the cohomological $`T_\ell`$, $`U_\ell`$, and the square |
| 4. coefficient change / functoriality | 3 | 1,142 | base change, equivariant retractions, Shapiro/projLine |
| 5. integral structure | 9 | 3,521 | torsion-freeness, integral basis, base change, denominators |
| 6. dimension theory | 4 | 1,180 | Euler-characteristic / genus bounds |
| 7. mod-$`p`$ eigenclass and boundary | 4 | 810 | integral eigenclass mod $`p`$; the Eisenstein boundary |

The full node list with line counts and the pin's English titles is the Appendix.
Three nodes are **interface-facing**: they are the only members of `R` whose
consumers outside `R` are endgame interfaces (all three feed interface 1) rather
than another member of `R`, route A / `finite_int_heckeAlgebra`, an analytic
node, or the retained re-proved node
`HeckeEis.exists_modularForm_heckeTLin_eq_smul_of_isEigensystemH1`:

* `exists_coeffH1par_projLineRepSL_equiv_parabolicHoms` (710) →
  `WeierstrassCurve.exists_ideal_heckeAlgebra_mul_two_…`;
* `exists_coeffH1par_map_of_equivariant_retraction` (174) → interface 1;
* `exists_coeffH1par_binaryFormRepSL_eigenclass_of_ideal_heckeAlgebra_of_ne_two`
  (61) → interface 1.

The rest feed `CuspForm.hasIntegralStructure_of_two_le` (route A, replaced by C′),
`HeckeEis.finite_int_heckeAlgebra` (the E-S proof of all-weight finiteness), or
the retained re-proved node above.

## 2. The mathematics

### 2.1 The period map

For a holomorphic $`f`$ on $`\mathbb{H}`$ and $`n \ge 0`$ (the weight is
$`k = n+2`$ for the cusp-form application), the pin's Eichler-integral predicate
`IsEichlerIntegral n f F` says, coefficient by coefficient, that the
$`V_n`$-valued function $`F`$ satisfies

$$F'(\tau) = f(\tau)\cdot(\tau X_0 + X_1)^n .$$

This is the pin's encoding of the classical Eichler integral of $`f`$; the
classical "integrate $`n`$ times" statement is recovered as the iterated
$`\partial_1`$-identity `hasDerivAt_eval_iterate_pderiv`, which at $`j = n`$
reads $`\frac{d}{d\tau}\mathrm{eval}_{(1,-\tau)}(\partial_1^n F) = n!\,f(\tau) - \cdots`$.
The existence input is the 12-node core
([015](015-weight-two-hecke-periods.md) §8): one-variable complex analysis on
$`\mathbb{H}`$ (a star-convex antiderivative and a Liouville-type boundedness
fact) plus polynomial algebra.

The **period cocycle** of $`F`$ is its failure to be $`\rho_n`$-equivariant,

$$z_F(\gamma) = F(\gamma i) - \rho_n(\gamma)F(i),$$

and it is a 1-cocycle, $`z_F(gh) = z_F(g) + \rho_n(g)z_F(h)`$. Two Eichler
integrals of the same $`f`$ differ by a constant binary form, hence their
cocycles differ by a coboundary; so $`f \mapsto [z_F]`$ is well defined, and the
three nodes `eichlerShimuraMap_add`, `eichlerShimuraMap_smul`,
`eichlerShimuraMap_eq_coeffH1parMk` record that it is ℂ-linear and computed by
any admissible $`F`$. **This is route B's `periodHom`, with one change: the
target is now the quotient $`H^1_{par}`$ rather than $`\mathrm{Hom}`$**, because
for $`n > 0`$ the coboundaries are nonzero.

**Injectivity** (`eichlerShimuraMap_injective`, 186 lines). If the period class
is a coboundary, $`z_F(\gamma) = (\rho_n(\gamma)-1)v`$, then
$`F_1 = F + v`$ satisfies $`F_1(\gamma\tau) = \rho_n(\gamma)F_1(\tau)`$: it is a
primitive of weight $`-n`$. Its evaluation against the line,
$`P(\tau) = \mathrm{eval}_{(1,-\tau)}F_1(\tau)`$, is then a holomorphic modular
form of weight $`-n \le 0`$, bounded at every cusp. A holomorphic form of
negative weight is zero, and of weight zero is constant
(`exists_eq_const_of_slash_invariant`, a 40-line lemma inside the proof), so
$`P`$ is constant; the ladder lemma `eq_zero_of_eval_eq_const` then forces
$`f = 0`$. This is the classical argument and it is the conceptual heart of the
whole packaging: **a nonzero cusp form has a nonzero period class because a
nonconstant holomorphic form cannot have nonpositive weight**.

### 2.2 Parabolic cohomology, and why the quotient is the right one

`coeffH1par ρ` is the quotient of the **parabolic** cocycles by the coboundaries,

$$Z^1_{par}(\Gamma, V) = \\{\\, z \in Z^1 : z(\gamma) \in (\rho(\gamma)-1)V
\text{ for every } \gamma \text{ with } \mathrm{tr}(\gamma)^2 = 4 \\,\\},
\qquad H^1_{par} = Z^1_{par}/B^1 .$$

In $`\mathrm{SL}_2(\mathbb{Z})`$ the condition
$`\mathrm{tr}(\gamma)^2 = 4`$ means $`|\mathrm{tr}\,\gamma| = 2`$, which (together
with the identity) is exactly the parabolic case: $`\gamma`$ fixes a cusp. So the
definition asks the cocycle to lie in the directions killed by $`\rho(\gamma)-1`$
on each cusp stabiliser — the parabolic or cuspidal part of $`H^1`$. The quotient
$`H^1/H^1_{par}`$ is the Eisenstein part, which is exactly what the node
`exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1` ("boundary
Hecke eigensystems arise from modular forms") pins down — a class outside the
parabolic image comes from a modular form, so the Eisenstein eigensystems are
form-theoretic rather than cohomological.

**At $`n = 0`$ the parabolic condition reads $`z(\gamma) = 0`$ on unipotents, and
$`B^1 = 0`$, so $`H^1_{par} = \mathrm{Hom}(\Gamma, \mathbb{C})_{\text{par}}`$.**
Route B defines this parabolic character module (`parabolicChars`) and then never
uses it, precisely because $`\mathrm{Hom}`$ of a finitely generated group is
already finitely generated (015 §5). The quotient is *the* thing route B hides.

The two structural facts the packaging needs about this quotient are the ones
the pin proves directly: the cohomological Hecke operator descends to it, and
coefficient change descends to it.

### 2.3 The two halves: the Eichler–Shimura isomorphism

Complex conjugation acts on $`V_n`$ coefficient-wise, is conjugate-linear and
involutive on functions, and descends to $`H^1_{par}`$
(`exists_coeffH1par_semilinearMap_starRingEnd`, 332 lines; the descent uses that
conjugation preserves cocycles and coboundaries). Composing with the period map
gives the anti-holomorphic period map

$$\overline{ES} = \Phi \circ ES,$$

and the packaging theorem
(`exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime`, 110 lines,
with the shorter `…_binaryFormRepSL` a specialisation) asserts:

$$ES : S_{n+2}(\Gamma) \hookrightarrow H^1_{par}(\Gamma, \mathrm{Sym}^n)
\quad\text{and}\quad
\overline{ES} : S_{n+2}(\Gamma) \hookrightarrow H^1_{par}(\Gamma, \mathrm{Sym}^n)$$

are both injective, their images are complementary
(`IsCompl`, `isCompl_range_eichlerShimuraMap_range_conj`), and both intertwine
the Hecke operators. Hence

$$H^1_{par}(\Gamma_0(N), \mathrm{Sym}^{k-2}) \\;\\cong\\; S_k(\Gamma_0(N)) \oplus \overline{S_k(\Gamma_0(N))}$$

as Hecke modules. That is the classical **Eichler–Shimura isomorphism**, and it
is genuinely more than route B: route B proves only *injectivity* of the
$`k = 2`$ period map, i.e. one half of the statement in the one case where the
second half is invisible.

The hard half is `range_eichlerShimuraMap_inf_range_conj_eq_bot` (1,325 lines):
if $`ES(f) = \Phi(ES(g))`$, then $`f = 0`$ (and symmetrically). Unwinding, this
reduces to the same negative-weight trick on the difference of two primitives,
and it is the place where the *definiteness* of the Petersson product is hiding.
It is the single largest node in `R`.

### 2.4 Hecke equivariance

The cohomological Hecke operator is restriction–corestriction through the
double coset $`\Gamma_0(N)\,\mathrm{diag}(\ell,1)\,\Gamma_0(N)`$:

$$T_\ell^{\mathrm{coc}}(z)(g) = \sum_q \rho_n((g\cdot q).\mathrm{out})
\bigl(a_\ell\bigl(z(\mathrm{conj}(\mathrm{transferAux}(g,q)))\bigr)\bigr),$$

the `coeffHeckeFun` of `Def_Gamma0CoeffCohomology.lean`; it preserves cocycles
and coboundaries, hence exists on $`H^1`$ and on $`H^1_{par}`$
(`exists_coeffH1par_linearMap_coeffHeckeFun`, 80 lines). The two 900- and
600-line nodes

```
T_ℓ^{coc}(ES f) = ES(T_ℓ f)      (good ℓ)
T_ℓ^{coc}(ES f) = ES(U_ℓ f)      (bad ℓ)
```

are the same telescoping/coset identity as route B §4: in each coset term the two
$`F`$-values are pushed to a common representative, the leftover differences are
periods, and the sum over the coset space telescopes. The difference from route B
is purely that the coefficients are now $`\mathrm{Sym}^n`$ and the identity has
to be checked *after the quotient* — the `coeffH1par_map_heckeT_comm` node
(113 lines) is the statement that coefficient change commutes with
$`T_\ell^{\mathrm{coc}}`$, which is what lets the conjugate map $`\Phi`$ commute
with Hecke in §2.3.

### 2.5 Coefficient change, Shapiro, and the projectiveline bridge

For a ring map $`\phi : R \to R'`$, coefficient extension on $`\mathrm{Sym}^n`$
descends to $`H^1_{par}`$ (`exists_coeffH1par_map_ringHom`, 258 lines) and
commutes with $`T_\ell^{\mathrm{coc}}`$. The interesting member of this group is

```
exists_coeffH1par_projLineRepSL_equiv_parabolicHoms  (710 lines)
```

which is a **Shapiro-type (induction) identification** — the pin's own English
title is "Shapiro's lemma for parabolic cohomology, Hecke-equivariantly". The
projectiveline coefficient system is the permutation module of functions on
$`\mathbb{P}^1(\mathbb{Z}/p)`$; the isomorphism is evaluation along the Ihara map
$`\iota_0 : \Gamma_0(Np) \to \Gamma_0(N)`$, and it reads

$$H^1_{par}\bigl(\Gamma_0(N), \mathrm{Ind}_{\Gamma_0(Np)}^{\Gamma_0(N)}K\bigr)
\\;\\cong\\; H^1_{par}\bigl(\Gamma_0(Np), K\bigr),$$

so at trivial coefficients the target is route B's carrier
`ModularCurve.Period.parabolicHoms`. This node is the *conceptual bridge between
the two routes*: route B's $`\mathrm{Hom}`$ carrier and the packaging's
$`H^1_{par}(\mathrm{Sym}^n)`$ carrier meet through induction on the
projectiveline. `exists_coeffH1par_map_of_equivariant_retraction` (174) is the
general functoriality statement behind it.

### 2.6 Integral structure

This is the largest group (9 nodes / 3,521 lines) and the general-weight
analogue of route B §5, with the quotient making it genuinely harder.

* `coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero` (138) —
  **torsion-freeness**: $`m\,x = 0`$, $`m \neq 0`$, forces $`x = 0`$.
* `coeffH1par_binaryFormRepSL_eq_zero_of_odd` (71) — $`H^1_{par}`$ vanishes for
  odd $`n`$, because $`-I`$ acts as $`-1`$ on $`\mathrm{Sym}^n`$ with $`n`$ odd,
  matching the vanishing of odd-weight forms.
* `coeffH1par_map_int_rat_injective` (426),
  `linearIndependent_coeffH1par_map_rat_complex` (470),
  `mem_span_range_coeffH1par_map_rat_complex` (471) — the base-change diagram
  $`\mathbb{Z} \to \mathbb{Q} \to \mathbb{C}`$: injective, preserves linear
  independence, and its image spans.
* `exists_basis_coeffH1par_int_complex` (316) — **the integral basis theorem**:
  a ℤ-basis of $`H^1_{par}(\mathbb{Z})`$ maps to a ℂ-basis of
  $`H^1_{par}(\mathbb{C})`$. The proof is elementary module theory: $`\Gamma_0(N)`$
  is finitely generated (finite index in $`\mathrm{SL}_2(\mathbb{Z}) = \langle S,T\rangle`$),
  so the parabolic ℤ-cocycles embed in $`\mathbb{Z}^S`$ for a finite generating
  set $`S`$ and are a finitely generated ℤ-module (ℤ Noetherian); torsion-freeness
  makes the quotient free; the base-change diagram matches ranks.
* `span_range_coeffH1par_map_int_complex_eq_top` (54),
  `exists_ne_zero_smul_eq_coeffH1par_map_int_rat` (789) — spanning and
  denominator clearing: every rational class is a nonzero integer multiple of an
  integral one.
* `exists_eq_prime_smul_of_coeffH1par_map_eq_zero` (786) — if a class dies under
  reduction mod $`p`$, it is $`p`$ times an integral class. This is the
  non-divisibility input for the eigenclass.

For route B the corresponding group is one observation: $`\mathrm{Hom}`$ of a
finitely generated group is finitely generated, and $`\mathrm{Hom}(A,\mathbb{C})`$
is spanned by $`\mathrm{Hom}(A,\mathbb{Z})`$. Nothing quotient-shaped, nothing
torsion-shaped.

### 2.7 Dimension theory

The finrank bounds are the standard dimension formula for cusp forms, counted
through the group action:

* `finrank_coeffH1par_top_add_le` (393) — for a representation $`W`$ of
  $`\mathrm{SL}_2(\mathbb{Z})`$,
  $`\dim H^1_{par}(W) + \dim\ker(W(S)-1) + \dim\ker(W(ST)-1) + \dim\ker(W(T)-1) \le \dim W`$,
  the Euler-characteristic bound from the presentation
  $`\mathrm{SL}_2(\mathbb{Z}) = \langle S, T \mid S^2 = (ST)^3 = 1\rangle`$ (with
  $`-I`$ acting trivially).
* `finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced` (500) — Shapiro
  monotonicity for the induction from $`\Gamma_0(N)`$ to the full group.
* `finrank_coeffH1par_le_two_mul_dimFormula` (120) and
  `finrank_coeffH1par_zero_le_two_mul_genusFormula` (167) — the bound
  $`\dim H^1_{par} \le 2\dim S_k(\Gamma_0)`$, with

$$\dim S_k(\Gamma_0(N)) = (k-1)(g-1) + \left\lfloor\frac{k}{4}\right\rfloor \nu_2
+ \left\lfloor\frac{k}{3}\right\rfloor \nu_3 + \left(\frac{k}{2}-1\right)c,$$

  where $`g`$ is the genus, $`\nu_2, \nu_3`$ the numbers of elliptic points of
  order $`2, 3`$ and $`c`$ the cusp count (`ModularCurve.genusFormula`, `nuTwo`,
  `nuThree`, `cuspCount`).

This is real geometry, and it is the part of the packaging that is **not really
Eichler–Shimura**: the same genus/elliptic-point/cusp data is needed by the
endgame's modular-curve work regardless (Riemann–Roch, $`J_0(N)`$).

**In the pin this group has exactly one consumer**: all four nodes are cited only
by `isCompl_range_eichlerShimuraMap_range_conj`, which uses the dimension count to
turn "two injective images meeting in 0" into "they sum to everything". Nothing
else in `R` — not the period map, not its injectivity, not the integral basis,
not the eigenclass — uses a finrank bound. So the dimension theory is the price
of the *complementarity half* of the classical theorem, and of nothing else.

### 2.8 The mod-$`p`$ eigenclass

From a nonzero eigenform $`f`$ of weight $`n+2`$ with eigenvalues $`\alpha_\ell`$
and a prime $`\mathfrak{m}' \ni p`$ such that $`\alpha_\ell \equiv a_\ell \pmod{\mathfrak{m}'}`$,
`exists_coeffH1par_int_modp_eigenclass_of_eigenform` (205) produces an integral
parabolic class $`y`$ that is *not* $`p`$-divisible and satisfies
$`T_\ell y \equiv a_\ell\,y`$ for all good $`\ell`$. Two rewrites follow: the
ideal-theoretic version from a maximal Hecke ideal (71), and the char-$`p`$
eigensystem version over a field $`K`$ (61), which is what interface 1 consumes.
This is the **Eichler–Shimura congruence realized on the integral cohomology
lattice**: the eigenclass exists integrally and reduces to a nonzero mod-$`p`$
Hecke eigenvector. It uses the integral basis (§2.6) and the non-divisibility
lemma, and it is the arithmetic payoff of the whole packaging.

## 3. What is essential, what is bookkeeping, what is geometry

**Conceptually essential** (the part worth understanding, and the part that makes
the packaging explanatory):

1. the period cocycle and its linearity;
2. injectivity via the negative-weight modular form;
3. the parabolic quotient as the cuspidal part, with the Eisenstein quotient on
   the boundary;
4. Hecke equivariance of the period map;
5. Shapiro/induction as the bridge to route B's carrier;
6. the conjugate half and the two-piece decomposition — essential for the
   classical theorem, but *not* used by any endgame-facing node (§2.3, §2.7, §5).

**Bookkeeping** (large, mechanical, and the reason the packaging is called
"bundled"): the repeated hypothesis "$`\Phi`$ is induced by coefficient change on
cocycles" in roughly ten statements; the coset/transfer reindexing; the
denominator-clearing and base-change diagrams. This is where most of the 10,789
lines go.

**Geometry** (§2.7): the dimension bounds. Not E-S, shared with the endgame.

## 4. Route B against the packaging

| | route B (weight 2) | packaging (all weights) |
|---|---|---|
| carrier | $`\mathrm{Hom}(\Gamma_0, \mathbb{C})`$, no quotient | $`H^1_{par}(\Gamma_0, \mathrm{Sym}^n)`$, parabolic quotient |
| period map | injective only | injective + complementarity (full E-S isomorphism) |
| anti-holomorphic half | absent | present (conjugate-linear involution) |
| Hecke action | coset sum on $`\mathrm{Hom}`$ | coset sum on the quotient |
| integral structure | trivial ($`\mathrm{Hom}`$ of f.g. group) | f.g. + torsion-free, integral basis, base change |
| dimension theory | none | genus / elliptic / cusp formula |
| weight | 2 | all |
| pin size | 4,308 lines, 1 file, closure 1 | 10,789 lines / 33 nodes, on top of the 2,301-line core, plus geometry |
| what it shows | the $`n = 0`$ slice where quotient and conjugate half vanish | the classical theorem |

Two honest points in route B's favour. First, route B's proof does not need the
dimension theory at all: it gets finiteness of the Hecke algebra from the
finitely generated lattice of $`\mathrm{Hom}`$, not from a dimension count, which
is why it is self-contained at closure 1. Second, route B is *complete* for what
it claims: the triple-algebra argument recovers the third (form-side) Hecke
action from the cocycle side, so the form-side finiteness is a consequence, not a
hypothesis.

Two honest points in the packaging's favour. First, it is the statement a reader
can understand as *Eichler–Shimura*, whereas route B is a special case whose
carrier has been stripped of the very structure (the quotient) that makes the
theorem a theorem. Second, it is uniform in the weight, so it needs no
form-side weight descent ([016](016-mod-p-weight-filtration.md)); the relaxed
route buys that uniformity back with the 12-node primitive plus route B, at the
price of keeping two carriers.

## 5. Verdict

The packaging is more interesting than route B and not harder *in ideas*: its
six essential steps are classical and each fits in a paragraph. It is harder *in
port cost*, and the cost splits cleanly: the quotient bookkeeping and the
integral structure are unavoidable if the carrier is to be $`H^1_{par}`$ at all,
while the conjugate half (2,000 lines) and the dimension theory (1,180 lines)
are the price of the *complementarity* statement alone and can be dropped if the
endgame is the target.

So:

* If the goal is to **understand** the Eichler–Shimura content, the packaging is
  the better object and route B should be read as its $`n = 0`$ shadow. This is
  the reason to keep this note.
* If the goal is to **port the endgame**, route B remains the better route, and
  the relaxed strategy of
  [../studies/eichler-shimura-bypass-scout.md](../studies/eichler-shimura-bypass-scout.md)
  §6 is not improved by porting all 33.
* There is a **middle route** worth naming, and the dependency graph makes it
  precise. The two groups that exist only for the *full classical isomorphism*
  are the anti-holomorphic half (group 2, 2,000 lines) and the dimension theory
  (group 6, 1,180 lines): the four dimension nodes have exactly one consumer, the
  complementarity proof, and the conjugate map is consumed only by the packaged
  `exists_eichlerShimura_…_forall_prime`. Everything else — the period map
  (group 1), Hecke equivariance (group 3), coefficient change and the
  Shapiro/projLine bridge (group 4), the integral structure (group 5) and the
  mod-$`p`$ eigenclass (group 7) — is what the endgame-facing nodes actually
  use. (The eigenclass needs the integral basis, so group 7 cannot be separated
  from group 5.) Porting groups 1, 3, 4, 5, 7 is **24 nodes / 7,609 lines** and
  skips **3,180 lines** that only the complementarity statement needs. Caveat:
  route A's own proof of `hasIntegralStructure_of_two_le` *does* consume the
  packaged isomorphism, so if the packaging is meant to supply door 1 in place
  of C′, groups 2 and 6 come back; under the relaxed route (C′ for door 1) they
  do not. So the middle route is not "the packaging minus the fun part": it is
  the packaging minus exactly the two halves of the statement the endgame never
  reads.

A concrete reason to prefer route B as the *first* artifact, independent of
taste: it is closure 1, so it can be checked and understood in isolation, while
the packaging sits on top of the analytic core *and* the modular-curve geometry,
so a port of it cannot be read independently of them. Route B is the better
teaching artifact; the packaging is the better reference statement.

## 6. Reproduction

The node list and line counts are the relaxed `R` of
[../studies/eichler-shimura-bypass-scout.md](../studies/eichler-shimura-bypass-scout.md)
§6, computed by the local tool `tools/deps/prune.py`
(`--scenario packaging`, pin `aa2d8b3`); the grouping is by inspection of the
`Theorems/Thm_HeckeEis_*.lean` statements and the pin's English titles. The
mathematical reading is from the pinned sources: `Def_HeckeEis_EichlerIntegral.lean`
(the primitive, `eichlerShimuraMap`), `Def_Gamma0CoeffCohomology.lean`
(`coeffCocycles`, `coeffCoboundaries`, `coeffH1par`, `IsParabolicCocycle`,
`coeffHeckeFun`), `Def_Gamma0CoeffCohomologyEigen.lean` (`coeffH1`,
`coeffH1parToH1`, `IsCoeffHeckeOnH1`, `IsEigensystemH1`), and the `S_` files of
the nodes below.

```bash
cd tools/deps && python3 - <<'PY'
import sys; sys.path.insert(0, '.')
from fltdata import FltData
from prune import FltPayoff, build_removed, DEFAULT_ROOT
d = FltData(); pay = FltPayoff(data=d)
port = pay.closure(pay.pid(DEFAULT_ROOT))
rem, _, _ = build_removed(pay, "packaging", port)
for i in sorted(rem, key=lambda j: (-pay.lines(j), d.qual(j))):
    print(f"{pay.lines(i):>5}  {d.qual(i)}\n        {d.title(i)}")
PY
```

## Appendix — the 33 nodes of `R`

Line counts are the pin's `S_`-file lines; titles are the pin's generated English
titles. Links are the `Theorems/` statement files at the pin
(`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_<stem>.lean`,
`<stem>` = the qualified name with dots replaced by underscores).

### 1. The period map (4 / 394)

| node (`HeckeEis.`) | lines | content |
|---|---:|---|
| `eichlerShimuraMap_eq_coeffH1parMk` | 48 | computed by any admissible Eichler integral |
| `eichlerShimuraMap_add` | 81 | additivity |
| `eichlerShimuraMap_smul` | 79 | ℂ-homogeneity |
| `eichlerShimuraMap_injective` | 186 | injectivity via the negative-weight form |

### 2. The two halves (5 / 2,000)

| node | lines | content |
|---|---:|---|
| `exists_coeffH1par_semilinearMap_starRingEnd` | 332 | conjugate-linear involution on $`H^1_{par}`$ |
| `isCompl_range_eichlerShimuraMap_range_conj` | 185 | the two images are complementary |
| `range_eichlerShimuraMap_inf_range_conj_eq_bot` | 1,325 | they meet only in 0 (the hard half) |
| `exists_eichlerShimura_coeffH1par_binaryFormRepSL` | 48 | the packaged isomorphism |
| `exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime` | 110 | the same with all Hecke operators |

### 3. Hecke equivariance (4 / 1,742)

| node | lines | content |
|---|---:|---|
| `exists_coeffH1par_linearMap_coeffHeckeFun` | 80 | the cohomological $`T_\ell`$ exists |
| `coeffH1par_map_heckeT_comm` | 113 | coefficient change commutes with $`T_\ell`$ |
| `eichlerShimuraMap_heckeTLin` | 907 | $`ES`$ intertwines $`T_\ell`$ (good $`\ell`$) |
| `eichlerShimuraMap_heckeULin` | 642 | $`ES`$ intertwines $`U_\ell`$ (bad $`\ell`$) |

### 4. Coefficient change and functoriality (3 / 1,142)

| node | lines | content |
|---|---:|---|
| `exists_coeffH1par_map_ringHom` | 258 | coefficient extension on $`H^1_{par}`$ |
| `exists_coeffH1par_map_of_equivariant_retraction` | 174 | equivariant retractions (interface 1) |
| `exists_coeffH1par_projLineRepSL_equiv_parabolicHoms` | 710 | Shapiro/projLine bridge to route B |

### 5. Integral structure (9 / 3,521)

| node | lines | content |
|---|---:|---|
| `coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero` | 138 | torsion-freeness |
| `coeffH1par_binaryFormRepSL_eq_zero_of_odd` | 71 | odd $`n`$ vanishes |
| `coeffH1par_map_int_rat_injective` | 426 | $`\mathbb{Z}\to\mathbb{Q}`$ injective |
| `linearIndependent_coeffH1par_map_rat_complex` | 470 | independence persists over ℂ |
| `mem_span_range_coeffH1par_map_rat_complex` | 471 | rational classes span over ℂ |
| `exists_basis_coeffH1par_int_complex` | 316 | integral basis maps to a ℂ-basis |
| `span_range_coeffH1par_map_int_complex_eq_top` | 54 | integral classes span |
| `exists_ne_zero_smul_eq_coeffH1par_map_int_rat` | 789 | nonzero integral multiples |
| `exists_eq_prime_smul_of_coeffH1par_map_eq_zero` | 786 | mod-$`p`$ kernel is $`p`$-divisible |

### 6. Dimension theory (4 / 1,180)

| node | lines | content |
|---|---:|---|
| `finrank_coeffH1par_top_add_le` | 393 | Euler-characteristic bound for $`\mathrm{SL}_2(\mathbb{Z})`$ |
| `finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced` | 500 | Shapiro monotonicity |
| `finrank_coeffH1par_le_two_mul_dimFormula` | 120 | $`\dim H^1_{par} \le 2\dim S_{n+2}`$ |
| `finrank_coeffH1par_zero_le_two_mul_genusFormula` | 167 | weight-2 bound $`2g`$ |

### 7. Mod-$`p`$ eigenclass and boundary (4 / 810)

| node | lines | content |
|---|---:|---|
| `exists_coeffH1par_int_modp_eigenclass_of_eigenform` | 205 | integral eigenclass mod $`p`$ |
| `exists_coeffH1par_int_modp_eigenclass_of_ideal_heckeAlgebra` | 71 | from a maximal Hecke ideal |
| `exists_coeffH1par_binaryFormRepSL_eigenclass_of_ideal_heckeAlgebra_of_ne_two` | 61 | char-$`p`$ eigensystem (interface 1) |
| `exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1` | 473 | the Eisenstein boundary is form-theoretic |
