# The Eichler–Shimura isomorphism

**Status.** Mathematical exposition, pinned to the FLT pin `aa2d8b3`. This note
is only about the mathematics of the Eichler–Shimura package — the classical
isomorphism and the constructions it rests on. The Lean inventory of the package,
the consumer map and the port plan are measurements and live in
[../studies/eichler-shimura-scout.md](../studies/eichler-shimura-scout.md) §2–§3
and
[../lean/topics/eichlerShimura/TOPIC-period-map-injectivity.md](../lean/topics/eichlerShimura/TOPIC-period-map-injectivity.md).
Companions: [015-weight-two-hecke-periods.md](015-weight-two-hecke-periods.md)
(the weight-2 period map, route B) and
[016-mod-p-weight-filtration.md](016-mod-p-weight-filtration.md) (the mod-$`p`$
weight filtration).

Fix $`\Gamma = \Gamma_0(N)`$ and, for $`n \ge 0`$, the coefficient system
$`V_n = \mathrm{Sym}^n`$ realized as binary forms of degree $`n`$ (`BinaryForm ℂ n`),
with representation $`\rho_n`$ (`binaryFormRepSL`) and Hecke endomorphism
$`a_\ell`$ (`binaryFormAlphaAdj`). The weight is $`k = n+2`$.

## 0. The statement

The classical **Eichler–Shimura isomorphism** is

$$H^1_{par}(\Gamma_0(N), \mathrm{Sym}^{k-2}) \\;\\cong\\; S_k(\Gamma_0(N)) \oplus \overline{S_k(\Gamma_0(N))}$$

as Hecke modules, the two summands being the holomorphic and anti-holomorphic
periods of the cusp forms.

**It is a decomposition, not a surjectivity.** The period map $`ES`$ of §1 is
injective, but its image is only the *holomorphic* half: the target has twice the
dimension of the source,

$$\dim_{\mathbb{C}} H^1_{par}(\Gamma_0(N), \mathrm{Sym}^{k-2}) \\;=\\; 2\dim_{\mathbb{C}} S_k(\Gamma_0(N)),$$

so $`ES`$ is never onto $`H^1_{par}`$ — it is an isomorphism onto one Hodge piece
$`F^1`$. What is bijective is the **doubled** map

$$E : S_k \oplus \overline{S_k} \longrightarrow H^1_{par},
\qquad E(f,g) = ES(f) + \overline{ES}(g),$$

and the theorem is the bijectivity of $`E`$, which splits into

* $`E`$ **injective** = $`ES`$ and $`\overline{ES}`$ injective **and** their
  images disjoint (§3) — the disjointness is a genuinely new statement, not a
  consequence of injectivity;
* $`E`$ **surjective** = the two images span (§7) — proved by a dimension count,
  not by exhibiting preimages.

So only one direction of one half is a "surjectivity", and it is not a formal
add-on to injectivity.

§1–§5 build the two maps and their Hecke equivariance; §3 proves the
injectivities and the disjointness; §6 supplies the integral lattice; §7 gives the
dimension count that turns "disjoint" into "complementary"; §8 is the arithmetic
consequence (the mod-$`p`$ eigenclass and the Eisenstein boundary). §9 records the
degenerate weight-2 case.

## 1. The period map

For a holomorphic $`f`$ on $`\mathbb{H}`$ and $`n \ge 0`$, the **Eichler
integral** of $`f`$ is a $`V_n`$-valued function $`F`$ with

$$F'(\tau) = f(\tau)\cdot(\tau X_0 + X_1)^n$$

coefficient by coefficient (the pin's `IsEichlerIntegral n f F`; the classical
"integrate $`n`$ times" statement is recovered as the iterated-$`\partial_1`$
identity `hasDerivAt_eval_iterate_pderiv`). Existence is a single-variable
complex-analysis input: a star-convex antiderivative plus a Liouville-type
boundedness fact ([015](015-weight-two-hecke-periods.md) §8).

The **period cocycle** of $`F`$ is its failure to be $`\rho_n`$-equivariant,

$$z_F(\gamma) = F(\gamma i) - \rho_n(\gamma)F(i),$$

and it satisfies the 1-cocycle identity
$`z_F(gh) = z_F(g) + \rho_n(g)z_F(h)`$. Two Eichler integrals of the same $`f`$
differ by a constant binary form, hence their cocycles differ by a coboundary;
so the period class $`[z_F]`$ depends only on $`f`$, and $`f \mapsto [z_F]`$ is
$`\mathbb{C}`$-linear. This is the pin's `eichlerShimuraMap`, landing in
$`H^1_{par}(\Gamma, \mathrm{Sym}^n)`$.

**Injectivity.** If the period class is a coboundary,
$`z_F(\gamma) = (\rho_n(\gamma)-1)v`$, then $`F_1 = F + v`$ satisfies
$`F_1(\gamma\tau) = \rho_n(\gamma)F_1(\tau)`$: it is a primitive of weight
$`-n`$. Its evaluation against the line,
$`P(\tau) = \mathrm{eval}_{(1,-\tau)}F_1(\tau)`$, is a holomorphic modular form of
weight $`-n \le 0`$, bounded at every cusp. A holomorphic form of negative weight
is zero and of weight zero is constant, so $`P`$ is constant; the ladder lemma
`eq_zero_of_eval_eq_const` then forces $`f = 0`$. This is the conceptual heart of
the construction: **a nonzero cusp form has a nonzero period class because a
nonconstant holomorphic form cannot have nonpositive weight**.

## 2. Parabolic cohomology

`coeffH1par` is the quotient of the **parabolic** cocycles by the coboundaries,

$$Z^1_{par}(\Gamma, V) = \\{\\, z \in Z^1 : z(\gamma) \in (\rho(\gamma)-1)V
\text{ for every } \gamma \text{ with } \mathrm{tr}(\gamma)^2 = 4 \\,\\},
\qquad H^1_{par} = Z^1_{par}/B^1 .$$

In $`\mathrm{SL}_2(\mathbb{Z})`$ the condition
$`\mathrm{tr}(\gamma)^2 = 4`$ means $`|\mathrm{tr}\,\gamma| = 2`$, which (together
with the identity) is exactly the parabolic case: $`\gamma`$ fixes a cusp. The
definition therefore asks the cocycle to lie in the directions killed by
$`\rho(\gamma)-1`$ on each cusp stabiliser — the parabolic or cuspidal part of
$`H^1`$. The quotient $`H^1/H^1_{par}`$ is the Eisenstein part, and the statement
that a class outside the parabolic image comes from a modular form
(`exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1`) is what
makes the Eisenstein eigensystems form-theoretic rather than cohomological.

The two structural facts needed about the quotient are that the cohomological
Hecke operator descends to it (§4) and that coefficient change descends to it
(§5).

## 3. The two halves

Complex conjugation acts on $`V_n`$ coefficient-wise, is conjugate-linear and
involutive on functions, and descends to an involutive conjugate-linear map
$`\Phi`$ on $`H^1_{par}`$ (it preserves cocycles and coboundaries). Composing with
the period map gives the **anti-holomorphic period map**

$$\overline{ES} = \Phi \circ ES.$$

The theorem (`exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime`) is
that $`ES`$ and $`\overline{ES}`$ are both injective, their images are
**complementary** (`IsCompl`), and both intertwine the Hecke operators. Together
this says the doubled map $`E`$ of §0 is an isomorphism: the holomorphic periods
form one half of $`H^1_{par}`$ and the anti-holomorphic periods the other.

`IsCompl` has two halves, and they are proved by different arguments.

* **Disjointness** — `range_eichlerShimuraMap_inf_range_conj_eq_bot`: $`ES(f) = \Phi(ES(g))`$
  forces $`f = 0`$ (and symmetrically). This is the hard half, and the pin's
  largest node (1,325 lines). Unwinding, it is the negative-weight trick applied
  to the difference of two primitives, and it is where the *definiteness* of the
  Petersson product is hiding — the Hodge–Riemann relation in this language. It
  does **not** follow from the injectivity of $`ES`$: two injective maps can have
  overlapping images.
* **Spanning** — `isCompl_range_eichlerShimuraMap_range_conj`: the two images sum
  to $`H^1_{par}`$. This is not proved by exhibiting preimages; it follows from
  the two injections, the disjointness, and the dimension bound
  $`\dim H^1_{par} \le 2\dim S_k`$ of §7 (which is why that § is not optional).

## 4. Hecke equivariance

The cohomological Hecke operator is restriction–corestriction through the double
coset $`\Gamma_0(N)\,\mathrm{diag}(\ell,1)\,\Gamma_0(N)`$:

$$T_\ell^{\mathrm{coc}}(z)(g) = \sum_q \rho_n((g\cdot q).\mathrm{out})
\bigl(a_\ell\bigl(z(\mathrm{conj}(\mathrm{transferAux}(g,q)))\bigr)\bigr),$$

the pin's `coeffHeckeFun`. It preserves cocycles and coboundaries, hence exists on
$`H^1`$ and on $`H^1_{par}`$, and

$$T_\ell^{\mathrm{coc}}(ES\,f) = ES(T_\ell f) \quad (\text{good } \ell),
\qquad
T_\ell^{\mathrm{coc}}(ES\,f) = ES(U_\ell f) \quad (\text{bad } \ell).$$

This is the telescoping/coset identity of route B §4: in each coset term the two
$`F`$-values are pushed to a common representative, the leftover differences are
periods, and the sum over the coset space telescopes. The only difference from
the weight-2 case is that the coefficients are now $`\mathrm{Sym}^n`$ and the
identity is checked after the quotient.

## 5. Coefficient change and Shapiro

For a ring map $`\phi : R \to R'`$, coefficient extension on $`\mathrm{Sym}^n`$
descends to $`H^1_{par}`$ (`exists_coeffH1par_map_ringHom`) and commutes with
$`T_\ell^{\mathrm{coc}}`$ (`coeffH1par_map_heckeT_comm`); the latter is what lets
$`\Phi`$ commute with Hecke in §3.

The interesting case is the **Shapiro-type (induction) identification**. The
projectiveline coefficient system is the permutation module of functions on
$`\mathbb{P}^1(\mathbb{Z}/p)`$; evaluation along the Ihara map
$`\iota_0 : \Gamma_0(Np) \to \Gamma_0(N)`$ gives

$$H^1_{par}\bigl(\Gamma_0(N), \mathrm{Ind}_{\Gamma_0(Np)}^{\Gamma_0(N)}K\bigr)
\\;\\cong\\; H^1_{par}\bigl(\Gamma_0(Np), K\bigr),$$

the pin's `exists_coeffH1par_projLineRepSL_equiv_parabolicHoms`. At trivial
coefficients the target is route B's carrier `ModularCurve.Period.parabolicHoms`,
so this identifies the general-weight carrier with the weight-2 one through
induction. `exists_coeffH1par_map_of_equivariant_retraction` is the general
functoriality behind it.

## 6. Integral structure

Over $`\mathbb{Z}`$ the parabolic cohomology is a lattice:

* **Torsion-freeness** (`…_int_eq_zero_of_smul_eq_zero`): $`m\,x = 0`$ with
  $`m \neq 0`$ forces $`x = 0`$.
* **Odd vanishing** (`…_eq_zero_of_odd`): $`H^1_{par}`$ vanishes for odd $`n`$,
  because $`-I`$ acts as $`-1`$ on $`\mathrm{Sym}^n`$ for odd $`n`$, matching the
  vanishing of odd-weight forms.
* **Base change** $`\mathbb{Z} \to \mathbb{Q} \to \mathbb{C}`$
  (`coeffH1par_map_int_rat_injective`,
  `linearIndependent_coeffH1par_map_rat_complex`,
  `mem_span_range_coeffH1par_map_rat_complex`): injective, preserves linear
  independence, and its image spans.
* **Integral basis** (`exists_basis_coeffH1par_int_complex`): a ℤ-basis of
  $`H^1_{par}(\mathbb{Z})`$ maps to a ℂ-basis of $`H^1_{par}(\mathbb{C})`$. The
  argument is elementary module theory: $`\Gamma_0(N)`$ is finitely generated
  (finite index in $`\mathrm{SL}_2(\mathbb{Z}) = \langle S, T\rangle`$), so the
  parabolic ℤ-cocycles embed in $`\mathbb{Z}^S`$ for a finite generating set
  $`S`$ and are a finitely generated ℤ-module (ℤ is Noetherian); torsion-freeness
  makes the quotient free, and the base-change diagram matches ranks.
* **Denominators** (`span_range_coeffH1par_map_int_complex_eq_top`,
  `exists_ne_zero_smul_eq_coeffH1par_map_int_rat`): every rational class is a
  nonzero integer multiple of an integral one.
* **Mod-$`p`$ divisibility**
  (`exists_eq_prime_smul_of_coeffH1par_map_eq_zero`): a class killed by reduction
  mod $`p`$ is $`p`$ times an integral class.

This is the general-weight analogue of route B §5, where $`\mathrm{Hom}`$ of a
finitely generated group is already finitely generated and torsion-free.

## 7. Dimension theory

The dimension count is the standard cusp-form formula, read through the group
action:

* `finrank_coeffH1par_top_add_le`: for a representation $`W`$ of
  $`\mathrm{SL}_2(\mathbb{Z})`$,

$$\dim H^1_{par}(W) + \dim\ker(W(S)-1) + \dim\ker(W(ST)-1) + \dim\ker(W(T)-1) \le \dim W,$$

  the Euler-characteristic bound from the presentation
  $`\mathrm{SL}_2(\mathbb{Z}) = \langle S, T \mid S^2 = (ST)^3 = 1\rangle`$ (with
  $`-I`$ acting trivially);
* `finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced`: Shapiro
  monotonicity for the induction from $`\Gamma_0(N)`$ to the full group;
* `finrank_coeffH1par_le_two_mul_dimFormula` and
  `finrank_coeffH1par_zero_le_two_mul_genusFormula`: the bound
  $`\dim H^1_{par} \le 2\dim S_k(\Gamma_0)`$, with

$$\dim S_k(\Gamma_0(N)) = (k-1)(g-1) + \left\lfloor\frac{k}{4}\right\rfloor \nu_2
+ \left\lfloor\frac{k}{3}\right\rfloor \nu_3 + \left(\frac{k}{2}-1\right)c,$$

  where $`g`$ is the genus, $`\nu_2, \nu_3`$ the numbers of elliptic points of
  order $`2, 3`$ and $`c`$ the number of cusps.

This is geometry rather than Eichler–Shimura, and it is exactly the
genus/elliptic-point/cusp data the modular-curve side needs anyway. Its role in
the isomorphism is narrow and precise: the two injections give
$`\dim(\mathrm{range}\,ES + \mathrm{range}\,\overline{ES}) = 2\dim S_k`$, the
disjointness of §3 makes the sum direct, and the bound
$`\dim H^1_{par} \le 2\dim S_k`$ turns the inclusion into an equality. So the
dimension count is what upgrades "two injective images meeting in 0" to
"complementary"; and conversely the isomorphism is what makes the bound an
identity, which is why §0 states the dimension equality as a consequence rather
than an input.

## 8. The mod-$`p`$ eigenclass and the Eisenstein boundary

Let $`f`$ be a nonzero eigenform of weight $`n+2`$ with eigenvalues
$`\alpha_\ell`$, and let $`\mathfrak{m}' \ni p`$ be a prime with
$`\alpha_\ell \equiv a_\ell \pmod{\mathfrak{m}'}`$. Then there is an integral
parabolic class $`y`$ that is *not* $`p`$-divisible and satisfies
$`T_\ell y \equiv a_\ell\,y`$ for all good $`\ell`$
(`exists_coeffH1par_int_modp_eigenclass_of_eigenform`; the same construction is
stated over a maximal Hecke ideal and over a char-$`p`$ field). This is the
**Eichler–Shimura congruence realized on the integral cohomology lattice**: the
eigenclass exists integrally and reduces to a nonzero mod-$`p`$ Hecke
eigenvector. It uses the integral basis of §6 together with the non-divisibility
lemma.

The complementary statement is the boundary
(`exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1`): an
eigensystem in $`H^1`$ that is not in the parabolic image comes from a modular
form. Together with §3 it gives the full classification of Hecke eigensystems in
$`H^1(\Gamma_0(N), \mathrm{Sym}^n)`$: those in $`H^1_{par}`$ are the holomorphic
and anti-holomorphic periods of cusp forms, and the rest are Eisenstein
(weight-$`(n+2)`$ forms).

## 9. The weight-2 degeneration

At $`n = 0`$ the coefficient system is trivial, every 1-coboundary vanishes
($`\rho(\gamma)v - v = 0`$), and

$$H^1_{par}(\Gamma, \mathbb{C}) = \mathrm{Hom}(\Gamma, \mathbb{C})_{\text{par}},$$

the parabolic additive characters — with no quotient. This is route B's carrier;
route B proves the $`k = 2`$ instance of the period map and its injectivity,
which is exactly the $`n = 0`$ slice of §1. It is the case where the quotient and
the anti-holomorphic half are both invisible; the general statement above is what
shows what those two add.

Finiteness of the Hecke algebra is *not* a role of route B: the pin's
$`\Gamma_1`$-basis integral structure (route C′) proves
`CuspForm.HasIntegralStructure` in every weight, and the general
`CuspForm.moduleFinite_heckeAlgebra` follows from it, so the $`k = 2`$ finiteness
is a corollary of the general one. Route B's distinctive content is the E-S map
at weight 2, nothing else.
