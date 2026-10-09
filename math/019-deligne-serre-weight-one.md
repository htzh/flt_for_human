# Deligne–Serre for weight one: odd Artin representations at the base of the modularity hierarchy

**Status.** Mathematical exposition, pinned to the FLT pin `aa2d8b3`. This note
explains the *mathematics* of the weight-one Deligne–Serre correspondence and
places it among the other modularity theorems the FLT development uses. The Lean
statements are collected in §9.

Companions: [011-tate-module.md](011-tate-module.md) (the $`\ell`$-adic
representations attached to elliptic curves and to eigenforms of weight
$`\ge 2`$), [017-eichler-shimura-isomorphism.md](017-eichler-shimura-isomorphism.md)
(the Eichler–Shimura isomorphism behind the weight-two case),
[013-integral-structure-gamma1-basis.md](013-integral-structure-gamma1-basis.md)
(a *different* result FLT takes from the same 1974 paper — Deligne–Serre's
Proposition 2.7, on the integral $`\Gamma_1`$-basis),
[014-chi-minus-3-eisenstein.md](014-chi-minus-3-eisenstein.md) (the weight-one
Eisenstein series $`E_1(1,\chi_{-3})`$ that drives the mod-$`3`$ congruence lift).

## 1. The theorem

Let $`N \ge 1`$, let $`\varepsilon`$ be a Dirichlet character modulo $`N`$, and let

$$f \\;=\\; \sum_{n \ge 1} a_n q^n, \qquad a_1 = 1,$$

be a normalized **weight-one cuspidal newform** of level $`N`$ and nebentypus
$`\varepsilon`$: a nonzero element of $`S_1(\Gamma_1(N), \varepsilon)`$ that is an
eigenform for every Hecke operator $`T_p`$ with $`p \nmid N`$. Deligne and Serre
proved in 1974 [DS74] that $`f`$ has a Galois representation, and that the
weight-one world is exactly the world of *Artin* representations:

> **Theorem (Deligne–Serre).** There is a continuous representation
> $$\rho_f : G_{\mathbb{Q}} \longrightarrow \mathrm{GL}_2(\mathbb{C})$$
> with **finite image**, unramified at every prime $`p \nmid N`$, such that for all
> such $`p`$
> $$\mathrm{tr}\\,\rho_f(\mathrm{Frob}_p) = a_p, \qquad \det\rho_f(\mathrm{Frob}_p) = \varepsilon(p).$$
> Equivalently, the characteristic polynomial of Frobenius is
> $$\mathrm{charpoly}\bigl(\rho_f(\mathrm{Frob}_p)\bigr) = X^2 - a_p X + \varepsilon(p).$$
> The representation $`\rho_f`$ is irreducible, has Artin conductor $`N`$ and
> determinant $`\varepsilon`$, and $`L(\rho_f, s) = L(f, s)`$. Conversely, every
> odd irreducible two-dimensional complex representation of $`G_{\mathbb{Q}}`$
> with conductor $`N`$ and determinant $`\varepsilon`$ is of the form $`\rho_f`$
> for a unique normalized weight-one cuspidal newform $`f`$ of level $`N`$ and
> nebentypus $`\varepsilon`$.

Three points of the statement carry the content.

**Finite image.** A continuous complex representation of a profinite group has
finite image, so $`\rho_f`$ is an *Artin representation*: it factors through
$`\mathrm{Gal}(L/\mathbb{Q})`$ for a finite extension $`L/\mathbb{Q}`$. This is the
feature that separates weight one from every other weight — see §2.

**Oddness is not a hypothesis, it is a consequence.** The determinant of
$`\rho_f`$ is $`\varepsilon`$, and weight-one forms force $`\varepsilon(-1) = -1`$
(§8). So the representation is odd, exactly as in Serre's conjecture.

**Irreducibility is equivalent to cuspidality.** An Eisenstein series of weight
one has a reducible attached representation, a sum of two Dirichlet characters;
a *cusp* form has an irreducible one. Since FLT only ever states the theorem for
$`f \in S_1`$, its conclusion is irreducibility. This also means the forward half
of the theorem is a statement about cusp forms only, and the "only if" direction
is what one checks.

The theorem is the two-dimensional case over $`\mathbb{Q}`$ of **Artin's
conjecture** (the holomorphy of $`L(\rho,s)`$ for a complex representation
$`\rho`$), and Deligne–Serre's proof settled it for the whole class of odd
two-dimensional representations. It is also the weight-one case of **Serre's
conjecture**, whose general form predicts that every odd irreducible mod-$`p`$
representation is modular of a prescribed weight and level; that general form is
now a theorem of Khare–Wintenberger [KW09], and its solvable-image and
weight-one cases are exactly the classical input.

## 2. What is special about weight one

For weight $`k \ge 2`$ the representation attached to an eigenform is
$`\ell`$-adic, not complex. Deligne's construction [Del71] produces, for each
prime $`\ell`$,

$$\rho_{f,\ell} : G_{\mathbb{Q}} \longrightarrow \mathrm{GL}_2(\overline{\mathbb{Q}}_\ell),$$

unramified outside $`N\ell`$, with
$`\mathrm{charpoly}(\rho_{f,\ell}(\mathrm{Frob}_p)) = X^2 - a_p X + \varepsilon(p) p^{k-1}`$
for $`p \nmid N\ell`$. It is built from the étale cohomology of the
$`(k-2)`$-fold fibre power of the universal elliptic curve over $`X_1(N)`$ (the
Kuga–Sato variety). At $`k = 2`$ this is the Tate module of the Jacobian
$`J_1(N)`$, and the arithmetic content is the Eichler–Shimura congruence
relation

$$\mathrm{Frob}_p^2 - T_p\\,\mathrm{Frob}_p + p = 0$$

on $`J_1(N)`$; this is the mechanism that attaches $`\rho_{E,\ell}`$ to an
elliptic curve via its modular parametrisation
([011](011-tate-module.md), [017](017-eichler-shimura-isomorphism.md)).

For $`k \ge 2`$ the image of $`\rho_{f,\ell}`$ is in general **infinite** — it is
open in a $`\ell`$-adic group, and the system is not Artin. Weight one is the
unique exception, and the reason is analytic:

* by **Rankin's method** (the Rankin–Selberg convolution of $`f`$ with itself,
  and its analytic continuation), the Hecke eigenvalues of a weight-one form are
  bounded algebraic integers: the $`a_p`$ lie in a fixed finite set of algebraic
  integers whose complex embeddings are bounded;
* for each $`\ell`$ one has the mod-$`\ell`$ representation obtained by reducing
  a congruent weight-two eigenform (§3), and the coefficient bound bounds the
  order of its image in $`\mathrm{GL}_2(\mathbb{F}_\ell)`$ independently of
  $`\ell`$;
* a compatible system whose ramification, traces and determinant are bounded has
  finite image, so the limit is an Artin representation.

This is precisely the shape of the 1974 proof: Rankin's bound, the mod-$`\ell`$
representations, a bound on subgroups of $`\mathrm{GL}_2(\mathbb{F}_\ell)`$, and
conclusion. The upshot is a correspondence that exists nowhere else in the
weight hierarchy: weight-one cusp forms are not just *modular*, they are
*finite-image Galois objects*, and one can go back and forth between the two
sides.

Weight one is also the one weight of the hierarchy where the *algebraic* route to
integrality is unavailable. For $`k \ge 2`$ the classical proof of integral structure identifies the
cusp space with a cohomology space $`H^1_{par}(\Gamma, \mathrm{Sym}^{k-2})`$ carrying
an integral structure from the period lattice, and transports integrality across the
comparison; the coefficient system needs $`k - 2 \ge 0`$, so at $`k = 1`$ there is
nothing to transport. The integrality weight one does use is the $`q`$-expansion
lattice, and it feeds the coefficient ring of one eigenform rather than the Hecke
algebra of a fixed level — §3.

## 3. The two directions, and the lifting that connects them

**Forward: form $`\to`$ representation.** One cannot feed a weight-one form
directly into Deligne's cohomological construction, which starts at weight two.
The bridge is the **Deligne–Serre lifting** (the *relèvement*). The key observation
is that multiplying a weight-one form by a weight-one **Eisenstein** series raises
the weight to two: if $`E`$ is modular of weight one and $`f`$ is modular of
weight one, then $`f E`$ is a weight-two cusp form, and the multiplier $`E`$ can be
chosen so that the reduction of $`f E`$ has the same Hecke eigenvalues as the
reduction of $`f`$.

**The multiplier.** The series that raises the weight is a weight-one Eisenstein
series $`E_1(1,\chi)`$ attached to a primitive odd Dirichlet character $`\chi`$
modulo $`L`$. It is built analytically — through the cotangent expansion of the
Weierstrass $`\zeta`$-function and the quasi-periods of the associated lattice
functions — and its $`q`$-expansion is

$$`E_1(1,\chi) \\;=\\; -\frac{1}{2L}\sum_{a \bmod L} a\,\chi(a) \\;+\; \sum_{n \ge 1}\Bigl(\sum_{d \mid n}\chi(d)\Bigr) q^n .`$$

Its constant term is the generalized Bernoulli number $`-B_{1,\chi}/2`$ and its
higher coefficients are the divisor sums $`\sigma_\chi(n)`$. For $`\ell = 3`$ and
$`\chi = \chi_{-3}`$ this is the series of
[014](014-chi-minus-3-eisenstein.md), whose non-constant coefficients are
divisible by $`6`$, hence by $`3`$. FLT proves both halves: the divisor-sum
$`q`$-expansion
(`ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd`) and
the analytic verification that the function is a weight-one form of the right
slash covariance and bounded at the cusp
(`EisensteinSeries.eisensteinG1_apply_smul_and_eisensteinG1_add`,
`EisensteinSeries.isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1`).

In the lifting one takes $`\chi`$ of conductor supported on the residual prime
$`\ell`$ — the Teichmüller character for odd $`\ell`$, the nontrivial character
modulo $`4`$ for $`\ell = 2`$ — normalizes $`E_1(1,\chi)`$ by its constant term,
and uses the congruence $`\chi(p)\,p \equiv 1`$ at good $`p`$. The product
$`f\,E_1(1,\chi)`$ is then a weight-two cusp form whose residual Hecke eigenvalues
agree with those of $`f`$.

**The relèvement, in general form.** The abstract step is weight-independent, and
FLT states it that way. If a cusp form $`h`$ of weight $`w`$ is an eigenform
*modulo* a prime of the coefficient ring $`R`$ — the Hecke relation holds after
applying $`\varphi : R \to \kappa`$ — and its reduction is nonzero, then a genuine
weight-$`w`$ eigenform $`g`$ exists whose eigenvalues reduce to the same data. The
proof is a lifting in the finite $`\mathbb{Z}`$-algebra generated by the Hecke
operators on the finite-dimensional space $`S_w`$: the $`q`$-expansion is
injective, so a residual eigenvector can be lifted and certified. This is
`DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr`; its
weight-one $`\to`$ weight-two instance, obtained by multiplying by the multiplier
above, is
`DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen`.
Once a genuine weight-two eigenform is available, Deligne's construction applies
and the compatible system over $`\ell`$ is pieced together; Rankin's bound (§2)
then shows the system is Artin.

**The coefficient ring, and Galois conjugation.** The Hecke eigenvalues of a
weight-one eigenform are algebraic integers, and the subalgebra $`R`$ they and the
nebentypus values generate inside $`\mathbb{C}`$,
$`R = \mathbb{Z}[\,a_p,\ \varepsilon(x)\ :\ p \nmid N,\ x \in \mathbb{Z}/N\,]`$,
is finite as a $`\mathbb{Z}`$-module. The finiteness is a
trace argument: the Hecke operators preserve an integral lattice in the
finite-dimensional $`S_1`$, and the eigenvalues of a family of operators preserving
a spanning lattice generate a finite $`\mathbb{Z}`$-algebra
(`Submodule.moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top`). Once $`R`$
is finite, each ring homomorphism $`\tau : R \to \mathbb{C}`$ produces a
*conjugate* eigenform: a normalized weight-one cusp form $`g`$ with
$`a_p(g) = \tau(a_p(f))`$ and $`\varepsilon_g = \tau \circ \varepsilon`$. The
eigenvector for the prescribed character is extracted from a minimal prime of the
finite algebra
(`DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul`), and the
rationality of its coordinates in a basis of rational operators is what makes the
conjugate form classical
(`Module.Basis.repr_mem_range_ratCast_of_forall_dual`,
`Module.Basis.exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast`); the
statement is
`DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen`.
This is the algebraic form of "the absolute Galois group permutes the normalized
weight-one newforms", and it is what lets the reductions at different primes be
compared.

**Which integrality this uses.** The lattice in that trace argument is the
$`\mathbb{Z}`$-span of the cusp forms of level $`\Gamma_1(N)`$ whose
$`q`$-expansion is integral, and its fullness is a weight-general statement about
the $`\Gamma_1`$-space: $`S_k(\Gamma_1(N))`$ is defined over $`\mathbb{Q}`$, and
across the finitely many $`\Gamma_0(N)`$-translates the denominators are bounded, so
the space has a basis whose $`\Gamma_0`$-slashes all have integral coefficients
(Deligne–Serre, Proposition 2.7). That is *not* the classical integral-structure
theorem. The classical theorem — for $`k \ge 2`$, the integrally expanded forms span
$`S_k(\Gamma_0(N))`$, so the Hecke algebra acting on it is a finite
$`\mathbb{Z}`$-module — is a different and downstream statement, and it follows from
the $`\Gamma_1`$ basis by one extra step: the trace over
$`\Gamma_1 \trianglelefteq \Gamma_0`$ of a form all of whose $`\Gamma_0`$-translates
are integrally expanded is integrally expanded, since it is their finite sum, while
the trace composed with restriction is multiplication by the index, so the
$`\Gamma_0`$-lattice is full-rank. The classical proof of that same theorem reaches
it instead through the Eichler–Shimura comparison and the period lattice.

The forward direction needs neither the comparison nor the $`\Gamma_0`$ statement.
The $`\Gamma_1`$ lattice runs the eigenvalue-algebra trace above, and the rationality
of the eigenvector's coordinates in a basis of rational operators supplies the Galois
conjugates; nothing there asks for the Hecke algebra of a fixed level to be finite.
The $`\Gamma_0`$ integral structure — a statement about the whole space rather than
about one eigenvalue algebra — is what the general-weight mod-$`\ell`$ theory
consumes; it too is reachable from the $`\Gamma_1`$ basis, in every weight and by the
same trace step, but that is an extra step the weight-one argument has no use for.
What is genuinely unavailable at $`k = 1`$ is the period-lattice route, and with it
the cohomological form of the argument.

**Converse: representation $`\to`$ form.** This is the harder half of [DS74], and
it is where the bijection is proved. Given an odd irreducible two-dimensional
complex representation $`\rho`$ of $`G_{\mathbb{Q}}`$ with finite image, one wants
a weight-one newform whose $`L`$-function is $`L(\rho,s)`$. The two sides are
matched by their functional equations: $`\Lambda(s,\rho)`$ satisfies the same
functional equation, with the same root number, as the completed $`L`$-function
of a weight-one form of conductor $`N`$ and nebentypus $`\det\rho`$. The proof
uses Weil–Langlands (automorphic induction and base change for $`\mathrm{GL}_2`$)
and a counting argument: the finite subgroups of
$`\mathrm{PGL}_2(\mathbb{C})`$ are cyclic, dihedral, $`A_4`$, $`S_4`$ or $`A_5`$,
every projective representation lifts to $`\mathrm{GL}_2`$, and the dimension of
the weight-one newform space equals the number of isomorphism classes of such
representations with the prescribed conductor and determinant. The dihedral case
is the classical theta series of a Hecke character of an imaginary quadratic
field; the exceptional `A_4`/`S_4`/`A_5` cases are the genuinely "exotic"
weight-one forms.

**The local factors.** The theorem is an equality of $`L`$-functions, and FLT
formalizes the local half as well: for a weight-one newform of level $`N`$ and a
Galois representation with the same Frobenius traces, the Euler factor at a good
prime is $`1 - a_p X + \varepsilon(p) X^2`$ (with $`X = p^{-s}`$), and the tame
level exponents at the bad primes agree with the Artin conductor. This
(`DeligneSerre.eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace`)
is what lets the converse produce a form at exactly the right level, not merely
some level.

## 4. Assembling the representation from residual data

The forward direction reaches $`\rho_f`$ by gluing its reductions modulo many
primes. Three algebraic facts do the work, and a fourth analytic fact lets them be
compared.

**Semisimple descent of a reducible residual representation.** Suppose a residual
representation has trace $`\chi_1 + \chi_2`$ and determinant $`\chi_1\chi_2`$ for
two characters $`\chi_1, \chi_2`$ of $`G`$ that a priori take values in a large
field $`\Omega`$, while both the sum and the product are known to lie in a
subfield $`\kappa \subseteq \Omega`$. Then $`\chi_1`$ and $`\chi_2`$ themselves
descend to $`\kappa`$: if $`\chi_1`$ is not $`\kappa`$-valued then
$`\chi_2 = \chi_1^{q}`$ for $`q = |\kappa|`$, so the pair is the Frobenius orbit
of one $`\kappa`$-valued character, and the diagonal representation descends to a
semisimple two-dimensional $`\kappa`$-representation with the prescribed trace and
determinant
(`DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range`).
The hypothesis on the sum and product is exactly what the residual data supplies,
and the conclusion is the semisimplicity asserted in the theorem.

**A representation of a finite group is determined by its character.** For
finite-image representations, equal characteristic polynomials at every group
element force conjugacy: a finite-order matrix has a trace that is a sum of roots
of unity, and the character determines the representation (Brauer–Nesbitt). FLT
uses the abstract finite-group form
(`Representation.exists_conj_eq_of_charpoly_eq_of_finite_range`) and the Galois
form, where the polynomials are known only at almost all Frobenius elements and
the density theorem below upgrades "almost all primes" to "all group elements"
(`GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel`).
It also uses the converse direction: a mod-$`\ell`$ representation of a finite
group of order prime to $`\ell`$ lifts to characteristic zero with matching
characteristic polynomials
(`Representation.exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard`).

**Gluing a complex representation from a residual family.** Given, for every
prime $`\ell`$, a mod-$`\ell`$ representation with
$`\mathrm{charpoly}(\mathrm{Frob}_p) = X^2 - t_p X + d_p`$, where $`t_p, d_p`$ lie
in a fixed finite $`\mathbb{Z}`$-algebra $`R`$, one wants a complex representation
with trace $`t_p`$ and determinant $`d_p`$. Two arithmetic observations settle it:
a nonzero element of a finite $`\mathbb{Z}`$-algebra is detected by infinitely many
primes, so candidates that agree modulo infinitely many primes agree in
$`\mathbb{C}`$; and the trace of a finite-order $`2 \times 2`$ matrix is a sum of
two roots of unity, which confines the possible traces to a finite set. The result
is `DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual`.

**The Frobenius-density input.** The upgrade from "almost all primes" to "all
group elements" is the qualitative Frobenius density theorem (Chebotarev): for a
finite Galois extension $`L/\mathbb{Q}`$, the primes whose Frobenius class lies in
a given conjugacy-stable set have a density, and it is positive exactly when the
set is nonempty. FLT proves the qualitative form it needs — not the exact density
— from the asymptotic of the degree-one prime sum, which is the analytic input
(`FrobeniusDensity.statement`, `FrobeniusDensity.degOneAsymptotic`,
`FrobeniusDensity.statement_of_degOneAsymptotic`).

## 5. Where it sits among the modularity theorems

The modularity theorems FLT uses are not separate proofs of one statement;
they are the different ranges of the dictionary between Galois representations
and automorphic forms, and Deligne–Serre is the weight-one base of the tower.

| theorem | objects | direction | weight | image of $`\rho`$ | role in FLT |
|---|---|---|---|---|---|
| Deligne [Del71] | eigenform $`\to`$ $`\ell`$-adic rep | forms $`\to`$ reps | $`k \ge 2`$ | infinite, $`\ell`$-adic | attaches $`\rho_{E,\ell}`$ once the curve is modular |
| Eichler–Shimura | $`S_2`$ $`\leftrightarrow`$ $`H^1`$ / $`J_1(N)`$ | both | $`2`$ | Tate module | the geometry and the $`\mathrm{Frob}^2 - T_p\mathrm{Frob} + p = 0`$ congruence |
| Wiles / Taylor–Wiles, $`R = T`$ | residual modular $`\Rightarrow`$ modular lift | reps $`\to`$ forms | $`k \ge 2`$ | $`\ell`$-adic | upgrades residual modularity of the Frey curve to modularity |
| Langlands–Tunnell | solvable projective image (cyclic, dihedral, $`A_4`$, $`S_4`$) | reps $`\to`$ forms | $`1`$ | finite | residual modularity mod $`3`$ for the Frey curve |
| Serre / Khare–Wintenberger [KW09] | every odd irreducible mod-$`p`$ rep is modular | reps $`\to`$ forms | optimal | finite mod $`p`$ | the general backdrop; FLT needs only the $`p = 3`$ solvable case |
| **Deligne–Serre [DS74]** | weight-one newform $`\leftrightarrow`$ odd 2-dim Artin rep | **both** | $`1`$ | **finite** | the base case, and the lifting that feeds weight two |

Two structural remarks.

**Deligne–Serre is the only bidirectional entry.** The weight $`\ge 2`$ side is
one-directional in practice: attaching a representation to a form is Deligne's
construction, while going back (modularity) is the hard theorem of Wiles and its
successors. At weight one the two directions are both available, the
representation is rigid (finite image), and the correspondence is a bijection.
This is why weight one can serve as the *input* to a modularity-lifting machine
rather than only as its output.

**Langlands–Tunnell is the solvable case, and it needs Deligne–Serre.** For a
mod-$`p`$ representation whose projective image is solvable, the representation is
automorphic; over $`\mathbb{Q}`$ this covers the dihedral, tetrahedral and
octahedral images by base change and automorphic induction (a cyclic projective
image is abelian and is handled by class field theory). It is the case
$`p = 3`$ that Wiles uses: there
$`\mathrm{PGL}_2(\mathbb{F}_3) \cong S_4`$ is solvable, so the Frey curve's
mod-$`3`$ representation falls inside Langlands–Tunnell, and the theorem realizes
it by a weight-one form. Deligne–Serre then attaches the Artin representation to
that form and, through the lifting, produces a *weight-two* mod-$`3`$ form — which
is the residual modularity that the $`R = T`$ machine consumes. In this sense
Deligne–Serre is the hinge between "solvable mod-$`3`$ representations are
automorphic" and "residual modularity can be lifted", i.e. between
Langlands–Tunnell and Wiles.

The reason FLT can stop at $`p = 3`$ is the **3–5 switch**: modularity lifting is
formalized for $`p = 3`$ and $`p = 5`$, and the switch of curves with isomorphic
$`5`$-torsion reduces the $`5`$-adic case to the $`3`$-adic one. So the
Langlands–Tunnell/Deligne–Serre input is needed only at $`3`$.

## 6. How FLT uses it: the mod-3 octahedral case

The FLT chain that carries the weight-one input is, in premise direction
(from the theorem down to its inputs):

```text
FreyPackage.frey_isModular
→ WeierstrassCurve.modularity_of_semistableModel
→ WeierstrassCurve.isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel
→ FLT.No2BridgeWiring.weightOneNewformExists_levelAtThree_not_cube_dvd
→ LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_not_nine_dvd_not_cube_dvd_of_natCard_inertia_eq_two_of_coprime
→ … (LanglandsTunnell cusp-pair chain) …
→ DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen
→ DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen
→ DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen
→ CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast
```

The target of the middle step, `No2BridgeWiring.weightOneNewformExists_not_cube_dvd`,
is a statement about a semistable integral Weierstrass curve $`W`$ with
$`W.\Delta \ne 0`$ and irreducible mod-$`3`$ representation. It produces a level
$`N`$ and an integral Hecke eigensystem $`a`$ with the character $`\chi_{-3}`$
such that $`N`$ is cube-free away from $`3`$ and

$$3 \mid \bigl(a_\ell - W.a_\ell^{\mathrm{model}}\bigr)$$

at every good prime $`\ell`$ of $`W`$. That congruence is exactly "the curve's
mod-$`3`$ representation is modular at weight two, at a controlled level": the
weight-one form supplied by Langlands–Tunnell has been moved to weight two by the
Deligne–Serre lifting, and it matches the curve modulo $`3`$.

All three faces of Deligne–Serre are used:

* **forward** (`exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` and its residual
  companion) — attaches the Artin representation to the weight-one form inside the
  Langlands–Tunnell cusp-pair chain;
* **lifting** (`CuspForm.WeightTwoModThreeCongruenceLift`, proved by
  `CuspForm.exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd`)
  — the weight-one form modulo $`3`$ becomes a weight-two form, and this is what
  `No2BridgeWiring` consumes;
* **converse** (`exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace`) —
  produces the weight-one form with the correct tame conductor, i.e. the Artin
  conductor, which is used by the Langlands–Tunnell octahedral realization.

The weight-one Eisenstein series that powers the lifting is the subject of
[014-chi-minus-3-eisenstein.md](014-chi-minus-3-eisenstein.md): an arithmetic
coincidence (the hexagonal-lattice representation numbers equal a divisor sum)
supplies the explicit series $`E_1(1,\chi_{-3}) \equiv 1 \pmod 3`$ that makes the
congruence work.

## 7. The same paper's other result

"Deligne–Serre" names two different things in this project, and they should not
be conflated.

1. The **weight-one/Artin correspondence** of §1, which is the subject of this
   note.
2. **Proposition 2.7** of the same paper, on the integral structure of the
   $`\Gamma_1(N)`$-basis of modular forms. This is the result
   [013-integral-structure-gamma1-basis.md](013-integral-structure-gamma1-basis.md)
   uses to prove the integral structure of $`S_k(\Gamma_0(N))`$ for every $`k`$.
   FLT's `DeligneSerre271` namespace formalizes this Proposition 2.7, not the
   weight-one correspondence.

The two results sit in the same paper because both come out of the same analytic
study of weight-one forms: the correspondence is the Galois-theoretic output, and
the integrality of the Hecke action is a by-product of the bounded-denominator
analysis that the correspondence needs.

## 8. Oddness: why a weight-one eigenform has odd nebentypus

The parity condition $`\varepsilon(-1) = -1`$ is often listed as a hypothesis, but
for weight one it is forced. For $`\gamma = -I \in \Gamma_0(N)`$ and $`k = 1`$
the slash action is

$$(f \mid_1 (-I))(\tau) = (0\cdot\tau + (-1))^{-1} f(-I\cdot\tau) = -f(\tau),$$

while the nebentypus rule gives $`f \mid_1 (-I) = \varepsilon(-1) f`$. Comparing
the two, $`-f = \varepsilon(-1) f`$, so $`\varepsilon(-1) = -1`$ unless
$`f = 0`$. (Equivalently, the automorphy factor of $`-I`$ in weight $`k`$ is
$`(-1)^k`$, and at odd weight the identity $`(-I)\cdot\tau = \tau`$ is compatible
with a nonzero form only when the character is odd.) This is the same computation
FLT performs inside the proof of the weight-one Deligne–Serre theorem: it derives
$`\varepsilon(-1) = -1`$ from the Hecke eigen-relation and $`f \ne 0`$, and feeds
it to the irreducibility criterion, rather than carrying oddness as a hypothesis.
So the FLT statement covers "weight-one *odd* cusp forms" without assuming
oddness.

## 9. Lean summary

The mathematics above is the classical theorem. FLT proves it in the strength its
modularity argument needs, in the `DeligneSerre.*` and `LanglandsTunnell.*`
namespaces. This section is the technical summary.

**The headline statement, in characteristic form.** The workhorse is

```lean
theorem DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)
    (R : Subalgebra ℤ ℂ) (hR : ∀ p, p.Prime → ¬ p ∣ N → ModularFormClass.qCoeff f p ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R)
    (k : Type) [Field k] [Finite k] (φ : R →+* k) :
    ∃ ρ : Γℚ →* GL (Fin 2) k, GaloisFactorsThroughFiniteLevel ρ ∧
      (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation ∧
      ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), (p : k) ≠ 0 →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            ((ρ σ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).charpoly =
              X ^ 2 - C (φ ⟨ModularFormClass.qCoeff f p, hR p hp hpN⟩) * X +
                C (φ ⟨ε (p : ZMod N), hε _⟩)
```

([`Thm_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen.lean`, lines 38–56](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen.lean#L38-L56)).
This is §1's characteristic polynomial, stated at a finite residue field $`k`$:
the representation is semisimple, factors through a finite level, is unramified
with trivial inertia at every good prime $`p`$ invertible in $`k`$, and has
$`\mathrm{charpoly}(\rho(\mathrm{Frob}_p)) = X^2 - \varphi(a_p)X + \varphi(\varepsilon(p))`$.

The characteristic-zero companion

`DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen`
([lines 48–62](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_DeligneSerre_exists_galoisRep_of_weightOne_qCoeff_hecke_eigen.lean#L48-L62))
lifts the residual system to $`\rho : G_{\mathbb{Q}} \to \mathrm{GL}_2(\mathbb{C})`$
and concludes `IsIrreducible`, with trace $`a_p`$ and determinant
$`\varepsilon(p)`$ — §1's complex statement.

**The ingredients.** The characteristic-zero theorem is assembled from:

* `DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen`
  — the Rankin-type second-moment bound $`\sum_p \|a_p\|^2 p^{-s} \le \log(1/(s-1)) + C`$
  of §2;
* `DeligneSerre.isIrreducible_matrixRepresentation_of_tsum_norm_trace_sq_le_log_of_odd`
  — irreducibility from that bound together with oddness;
* the oddness lemma `apply_neg_one_eq` in the $`S\_`$ file, which derives
  $`\varepsilon(-1) = -1`$ (§8);
* `DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual`
  — promotion of a compatible family of residual characteristic polynomials to a
  complex representation with the prescribed traces and determinants;
* `DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen`
  and `…_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_…` — the
  finiteness of the coefficient ring, so that the residual data really is finite
  (§2's "boundedness" made into a finite $`\mathbb{Z}`$-algebra);
* `DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen`
  — the general-$`\ell`$ Deligne–Serre lifting of §3, which is what makes the
  residual representation exist at all;
* `DeligneSerre.eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace`
  and `DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace`
  — the local factors and the converse/level statement of §3.

**The coupling with Langlands–Tunnell.** The Langlands–Tunnell side is packaged by
`CuspForm.IsWeightOneChiNegThreeRealized`
(`Def_LanglandsTunnell_WeightOneRealizationCarriers.lean#L15`) and the lifting by
`CuspForm.WeightTwoModThreeCongruenceLift` (same file, line 38). The bridge
theorem `LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_of_deligneSerre_output`
takes a weight-one form whose coefficients match a mod-$`3`$ representation and
returns the $`\mathbb{Z}[\sqrt{-2}]`$-valued eigensystem; the weight-one form with
the right conductor comes from
`DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace`; and the
weight-one $`\to`$ weight-two mod-$`3`$ step is
`CuspForm.exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd`
("weight-one eigensystem realised mod 3 in weight two"). These are the three
constituents of `FLT.No2BridgeWiring.weightOneNewformExists_not_cube_dvd`
([line 61](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FLT_No2BridgeWiring_weightOneNewformExists_not_cube_dvd.lean#L61)).

## References

* [P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. Éc.
  Norm. Supér. (4) **7** (1974), 507–530](https://www.numdam.org/item/ASENS_1974_4_7_4_507_0/) —
  the theorem of §1 and Proposition 2.7 of §7.
* [P. Deligne, *Formes modulaires et représentations $`\ell`$-adiques*, Sém.
  Bourbaki 1968/69, Exp. 355 (1971), 139–172](https://www.numdam.org/item/SB_1968-1969__11__139_0/) —
  the weight $`\ge 2`$ construction of §2.
* [H. Darmon, *Artin representations attached to forms of weight one*, McGill
  lecture notes 26–27](https://www.math.mcgill.ca/darmon/courses/11-12/nt/notes/lecture26.pdf) —
  a modern exposition of the proof strategy of §3.
* [C. Khare and J.-P. Wintenberger, *Serre's modularity conjecture (I)*, Invent.
  Math. **178** (2009), 485–504](https://link.springer.com/article/10.1007/s00222-009-0205-7) —
  Serre's conjecture of §1/§5.
