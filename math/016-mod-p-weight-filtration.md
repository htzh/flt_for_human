# The mod-$`p`$ weight filtration, and the gap in the Eichler–Shimura bypass

**Status.** This note explains one open problem — the "gap" — that decides whether
the analytic Eichler–Shimura period map can be dropped from the FLT endgame. It
gives the motivation, the mathematics of the gap, and the routes around it; the
Lean counterpart is collected in §8. Background:
[015-weight-two-hecke-periods.md](015-weight-two-hecke-periods.md) (route B, the
weight-two period map), [013-integral-structure-gamma1-basis.md](013-integral-structure-gamma1-basis.md)
(route C′, integrality), and
[../studies/eichler-shimura-bypass-scout.md](../studies/eichler-shimura-bypass-scout.md)
(the measurements this note is distilled from).

## 1. Motivation

To attach a two-dimensional mod-$`p`$ Galois representation to a Hecke eigenform,
the pin's proof turns the eigenform into a class in the group cohomology
$`H^1(\Gamma_0(N), \mathrm{Sym}^{k-2})`$ by an Eichler integral, and it is the
Hecke-eigenvector property of that class that the rest of the argument consumes.
That period map is the whole of the "analytic Eichler–Shimura" package — 213
modules and 71,865 lines in the endgame — and it is the only genuinely analytic
input on the critical path.

At weight 2 the same construction degenerates to something much smaller. The
period of a weight-two cusp form is an additive character
$`\Gamma_0(N) \to \mathbb{C}`$, i.e. an element of
$`\mathrm{Hom}(\Gamma_0(N), \mathbb{C})`$, with no cohomology quotient at all: at
trivial coefficients every coboundary vanishes, so "cocycle" and "class" coincide.
That weight-two theory is already written in the pin, self-contained (route B),
and it is also where the arithmetic Eichler–Shimura congruence lives —
$`\mathrm{Frob}^2 - T_\ell\,\mathrm{Frob} + \ell = 0`$ on the Jacobian of
$`X_0(N)`$. If the relevant Hecke eigenvector could always be produced at weight
two, all of the analytic package would be bypassed.

So the question is:

> Can a mod-$`p`$ Hecke eigenform of arbitrary weight $`k`$ be moved to weight 2
> without the period map?

The first half of the answer is classical and already available: the weight can
always be brought into the bounded window $`2 \le k' \le p+1`$ (§4). The second
half — from an interior weight in that window to weight 2 — is the gap (§5–§6).

## 2. The Hecke action sees the weight only modulo $`p-1`$

Fix a prime $`p`$, a field $`F`$ of characteristic $`p`$, and a level $`N`$ with
$`p \nmid N`$. On $`q`$-expansions the Hecke operator $`T_\ell`$ ($`\ell \neq p`$)
in weight $`k`$ is

$$(T_\ell f)(q) = \sum_{n \ge 1} a_{n\ell}(f) q^n + \ell^{k-1} \sum_{n \ge 1} a_n(f) q^{n\ell}.$$

The weight appears in exactly one place: the factor $`\ell^{k-1}`$. Consequently
two weights $`k`$ and $`k'`$ induce the *same* operator on every $`q`$-expansion
as soon as $`\ell^{k-k'} = 1`$ for every good $`\ell`$, that is, as soon as

$$(p-1) \mid (k - k').$$

When this holds, an eigenform of weight $`k`$ is *the same $`q`$-series* as an
eigenform of weight $`k'`$, with the same eigenvalues. The weight is thus only a
class in $`\mathbb{Z}/(p-1)`$ as far as the Hecke action is concerned.

The Galois side sees the same invariant and nothing more: a weight-$`k`$
eigenform has

$$\det \rho = \chi^{k-1}, \qquad \chi^{\\,p-1} = 1,$$

so $`k`$ is determined by $`\det\rho`$ only modulo $`p-1`$.

One caveat fixes the parity. The pin's $`q`$-expansion lattice is spanned by
reductions of *classical* forms with integral coefficients, and a classical form
of odd weight vanishes, because $`-I \in \Gamma_0(N)`$ acts on $`\mathbb{H}`$ by
the identity while the weight-$`k`$ automorphy factor is $`(-1)^k`$. So odd
weights carry no forms in this lattice, and all effective weights are even.

## 3. Hasse and the Serre derivative: the two weight shifts

Two operations change the weight, and they behave very differently.

**The Hasse invariant.** $`A = E_{p-1} \bmod p`$ is a modular form of weight
$`p-1`$ whose $`q`$-expansion begins with $`1`$. Its weight is $`0`$ in
$`\mathbb{Z}/(p-1)`$, and multiplication by $`A`$ is Hecke-equivariant and does
not change eigenvalues. So multiplication by $`A`$ moves a form inside its weight
class; it can never change the class.

**The Serre derivative.** Put $`\theta = q\,\frac{d}{dq}`$ and, for weight $`k`$,

$$D_k = 12\\,\theta - k\\,E_2,$$

where $`E_2`$ is the quasimodular Eisenstein series of weight 2. $`D_k`$ is the
Serre derivative: it maps weight $`k`$ to weight $`k+2`$ and is Hecke-equivariant.
On $`q`$-expansions a direct computation gives

$$\theta \circ T_\ell^{(k)} = \ell^{-1}\\, T_\ell^{(k+2)} \circ \theta .$$

So $`\theta`$ carries a weight-$`k`$ eigenform with eigenvalues $`\lambda_\ell`$ to
a weight-$`(k+2)`$ eigenform with eigenvalues $`\ell\,\lambda_\ell`$: it changes the
weight class by $`2`$ and twists the eigenvalues by one factor of $`\ell`$.
Iterating, a weight-$`k'`$ eigenform that is $`\theta^m`$ of a weight-$`(k'-2m)`$
eigenform has eigenvalues $`\ell^{-m}`$ times those of the lower-weight form.

This $`\theta`$ is the form-side shadow of the degree shift $`n \mapsto n+2`$ in
$`H^1(\Gamma_0, \mathrm{Sym}^n)`$, and its $`\ell`$-twist is the shadow of the
$`\ell^{n/2}`$ eigenvalue twist in the cohomology-side reduction. That is why the
two accounts of the weight have to agree.

One point of bookkeeping deserves emphasis, because it is where the mod-$`p`$
subtlety sits: $`E_2`$ is only quasimodular, so the operator with the clean
weight-$`(k+2)`$ membership is the combination $`D_k`$; $`\theta`$ alone is only
known to land in weight $`k+(p+1)`$. The gap between the two statements is the
$`E_2`$-multiple, and it is the p-depletion phenomenon that closes it: the series
$`E_2 - p\,E_2(q^p)`$ is a genuine weight-two modular form with integral
$`q`$-coefficients, and it agrees with $`E_2`$ modulo $`p`$. So $`E_2`$ behaves
like a weight-two object on the $`q`$-expansion lattice, and the combination
$`D_k`$ really does raise the weight by $`2`$.

## 4. Reduction to the canonical window

Because the weight is only a class modulo $`p-1`$, one can always choose a
representative in the window

$$2 \le k' \le p+1 .$$

This interval contains exactly one representative of each class modulo $`p-1`$,
except that the class of $`2`$ is represented twice, by $`2`$ and by $`p+1`$. With
the parity constraint of §2 the effective window is
$`\{2, 4, 6, \dots, p-1, p+1\}`$.

The reduction is a filtration argument. If the form is Hasse-divisible — it lies
in the Hasse image from weight $`k-(p-1)`$ — then its weight drops by $`p-1`$ and
the eigenvalues are unchanged. If it is not, it is primitive at its own weight,
and the filtration either already has the weight inside the window or dispatches
the primitive part to a core construction that returns a form in the window with
a twisted eigenvalue system. Iterating gives the statement:

> Every mod-$`p`$ eigenform of weight $`k \ge 2`$ is, after an $`\ell^{j}`$ twist of
> its eigenvalues, an eigenform of some canonical weight $`k'`$ with
> $`2 \le k' \le p+1`$ and $`(p-1) \mid (k-k')`$.

The $`\ell^{j}`$ twist in the statement is the twist that the primitive/core part
of the filtration picks up; it is tracked because the downstream argument needs
the exact eigenvalue relation.

## 5. The gap

The canonical window is not weight 2, and the class is an invariant, so the
reduction cannot be pushed further by relabelling:

- **Class $`2`$ is free.** The two representatives are $`k' = 2`$ and
  $`k' = p+1`$, and they have identical Hecke action by §2. They are also
  connected by a level–weight exchange: a weight-$`(p+1)`$ form whose
  $`q^{pn}`$ coefficients vanish is a weight-two form at level $`Np`$. This is
  the case that is already formalized.
- **Interior even weights are the gap.** Let $`4 \le k' \le p-1`$ be the
  canonical representative of a class $`c = k' \not\equiv 2`$. A weight-two form
  has class $`2 \neq c`$, so its Hecke eigenvalues differ from those of the
  weight-$`k'`$ eigenform by the nontrivial character $`\ell^{k'-2}`$; no
  relabelling can remove the discrepancy. The form itself has to be moved, and the
  only operator that moves it is $`\theta`$. Descending $`m = (k'-2)/2`$ steps
  would produce a weight-two eigenform with eigenvalues

$$\mu_\ell = \ell^{-m}\\,\lambda_\ell .$$

So the gap is exactly the following statement.

> **Gap.** For even $`k'`$ with $`4 \le k' \le p-1`$, a mod-$`p`$ Hecke eigenform
> of weight $`k'`$ (cuspidal, with the standard level and ordinarity conditions)
> lies in the $`\theta`$-descent of a weight-two eigenform — at a controlled
> higher level — with eigenvalues twisted by $`\ell^{-(k'-2)/2}`$.

The level must rise: the weight-two object is not a level-$`N`$ form in general,
just as in the class-$`2`$ case it lives at level $`Np`$. The correct shape is
therefore a **level–weight exchange**, not an inclusion at fixed level.

## 6. Why the last step has content

It is worth seeing why the gap is not a formality, since "iterate $`\theta^{-1}`$"
sounds automatic.

**$`\theta`$ is not surjective.** The Serre derivative
$`\theta: M_{k-2} \to M_k`$ is injective up to the $`p`$-power series (its kernel
is the image of $`F[[q^p]]`$ under the $`q`$-expansion map), but it is far from
surjective; the $`\theta`$-filtration of $`M_k`$ has graded pieces consisting of
*primitive* forms of weights $`k, k-2, k-4, \dots`$. A general weight-$`k`$ form is a sum of
$`\theta`$-powers of primitive forms of several weights, and it need not be in
$`\theta(M_{k-2})`$. The classical example is weight 12: over $`\mathbb{C}`$ the
cusp form $`\Delta`$ spans $`S_{12}`$ while $`S_{10} = 0`$, so $`\Delta`$ is
primitive at weight 12 and is not a $`\theta`$-derivative at any lower weight.

**For eigenforms the filtration still does not collapse.** The graded pieces of
the $`\theta`$-filtration are Hecke-stable, but the piece of weight $`j`$ carries
eigenvalues twisted by $`\ell`$ relative to the piece of weight $`j-2`$. A
simultaneous eigenform for all $`T_\ell`$ is therefore (barring coincidences)
confined to a single graded piece, so its primitive weight can be genuinely
interior.

**What saves it is the twist.** On the Galois side, the representation
$`\rho \otimes \chi^{-(k'-2)/2}`$ has determinant $`\chi`$, i.e. weight 2; by
Serre's conjecture (a theorem) it is modular of weight 2, at a level that grows
with the conductor of the twist. So the weight-two eigenform exists; what is
missing is a *form-theoretic* realization of it, i.e. the level–weight exchange
that extracts it from the weight-$`k'`$ form. That is the classical content of
the gap, and it is why the statement has a real proof obligation rather than being
a change of notation.

## 7. Routes past the gap

**A. Prove the general level–weight exchange (form side).** Generalize the
class-$`2`$ statement to every interior even weight: an eigenform of weight $`k'`$
at level $`N`$ yields a weight-two eigenform at level $`Np^{m}`$ with eigenvalues
$`\ell^{-m}\lambda_\ell`$, $`m = (k'-2)/2`$. The ingredients are the
$`\theta`$-filtration, the Hasse divisibility criterion, and the $`p`$-depletion
bookkeeping that already appears in the class-$`2`$ case. This is the
mathematically direct route, it stays inside the "tame" additive-character
carrier, and it is the only route that removes the analytic package outright.

**B. Build the general-weight eigenclass geometrically (cohomology side).**
Instead of lowering the weight, construct the Hecke eigenvector in the
general-weight cohomology directly: realize the de Rham or Hodge–Tate model of
$`H^1(\Gamma_0(N), \mathrm{Sym}^{k-2})`$ (Kuga–Sato variety, or the de Rham
cohomology of the universal elliptic curve), and produce the eigenclass from the
mod-$`p`$ form via the geometric Eichler–Shimura congruence. This is standard
mathematics but heavy formalization, and it re-introduces exactly the
general-weight cohomology the bypass was meant to avoid.

**C. Hybrid: transport the weight-two class geometrically.** Use the geometric
operators (Hasse, $`\theta`$) realized on the function-field or Jacobian model to
move the weight-two eigenclass of route B along the filtration, then read off the
weight-$`k'`$ eigenvector. This is the geometric counterpart of A and may be
cheaper where the function-field model already exists.

**D. Fallback: keep the analytic period map.** The pin's Eichler–Shimura map
supplies the degree-$`(k-2)`$ eigensystem directly, at the cost of the analytic
core — twelve modules and 2,301 lines, not the whole package.

Routes A and C are the ones that preserve the point of the bypass; B is the
honest but expensive alternative; D bounds the loss if the gap stays open.

## 8. Lean summary

The mathematics above is the mod-$`p`$ weight filtration. The pin formalizes its
pieces without naming the filtration as such; the relevant declarations are these.

**Weight-dependent Hecke action and the class invariant.**
`ModPForms.heckePS` is the operator above, and `heckePS_congr_weight` records that
it depends on the weight only through $`\ell^{k-1}`$. The consequence
$`(p-1) \mid (k-k') \Rightarrow`$ same eigenform is
`isModPEigen_congr_weight`. Odd weights are empty by
`ModPForms.modPMod_eq_bot_of_odd` (and `CuspForm.eq_zero_of_odd_gamma0` at the
level of forms).

**$`\theta`$ and the Serre derivative.** `ModPForms.thetaPS` is
$`\theta = q\,d/dq`$; the Serre-derivative identity is
`smul_thetaPS_sub_smul_mem_modPMod_add_two`
($`12\theta\varphi - k E_2\varphi \in \mathrm{modPMod}(k+2)`$), with the product
rules `thetaPS_add_smul_mul_mem_modPMod_add_two` and
`smul_mul_thetaPS_sub_smul_thetaPS_mul_mem_modPMod_add_add_two`. The coarse
membership `thetaPS_mem_modPMod_add_of_mem` records the $`k \mapsto k+(p+1)`$ shift
discussed in §3, and the non-membership criterion
`thetaPS_not_mem_modPMod_add_two_of_not_mem_sub_of_not_dvd` is the first half of
the "primitive" behaviour of §6.

**Hasse.** `modPMod_le_modPMod_add_sub_one` is the inclusion
$`\mathrm{modPMod}(k) \subseteq \mathrm{modPMod}(k+(p-1))`$, and
`mem_modPMod_sub_of_qP_mul_mem` is the conditional drop by $`p-1`$ (it inverts the
Hasse step when $`E_2\varphi`$ lands in weight $`k+2`$).

**The reduction to the window.** The packaged statement is
`ModPForms.exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure`;
its proof runs the trichotomy `filtration_trichotomy` (weight drops by $`p-1`$ while
the form stays Hasse-divisible) and dispatches the primitive case to a
`CoreRow`/`SSDatum` construction. The `SSDatum` built there is the weight
filtration in module form: mod-$`p`$ modules indexed by weight, a residue map with
`res_ker : res φ = 0 \Rightarrow φ \in \mathrm{modPMod}(k-(p-1))`, and a weight
periodicity $`S_k \cong S_{k+(p+1)}`$.

**The descents to weight 2 that exist.** Only two cases are formalized. The
class-$`2`$ case is
`ModPForms.mem_modPMod_two_of_mem_modPMod_of_forall_coeff_mul_eq_zero` (weight
$`p+1`$ with vanishing $`q^{pn}`$ coefficients lies in weight 2) together with the
level–weight exchange
`ModPForms.modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two`
($`\mathrm{modPCusp}(N, p+1) \subseteq \mathrm{modPCusp}(Np, 2)`$); the char-3
weight-4 case is
`ModPForms.mem_modPMod_two_of_mem_modPMod_four_of_forall_coeff_three_mul_eq_zero_of_exists_prime_dvd_mod_three_eq_two`.

**What is missing.** No declaration anywhere in the pin takes an interior even
weight $`4 \le k' \le p-1`$ to weight 2. That absent level–weight exchange is the
gap of §5, and it is the single statement on which routes A and C of §7 depend.
