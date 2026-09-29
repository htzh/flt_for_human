# Deligne–Serre for weight one: odd Artin representations at the base of the modularity hierarchy

**Status.** Mathematical exposition, pinned to the FLT pin `aa2d8b3`. This note
explains the *mathematics* of the weight-one Deligne–Serre correspondence and
places it among the other modularity theorems the FLT development uses. The Lean
statements, the endgame route and the porting distance are collected in §8.

Companions: [011-tate-module.md](011-tate-module.md) (the $`\ell`$-adic
representations attached to elliptic curves and to eigenforms of weight
$`\ge 2`$), [017-eichler-shimura-isomorphism.md](017-eichler-shimura-isomorphism.md)
(the Eichler–Shimura isomorphism behind the weight-two case),
[013-integral-structure-gamma1-basis.md](013-integral-structure-gamma1-basis.md)
(a *different* result FLT takes from the same 1974 paper — Deligne–Serre's
Proposition 2.7, on the integral $`\Gamma_1`$-basis),
[014-chi-minus-3-eisenstein.md](014-chi-minus-3-eisenstein.md) (the weight-one
Eisenstein series $`E_1(1,\chi_{-3})`$ that drives the mod-$`3`$ congruence lift),
and [../studies/flt-non-frey-segments.md](../studies/flt-non-frey-segments.md) §3.4
(the segment and the frontier measurement).

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
(§7). So the representation is odd, exactly as in Serre's conjecture.

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

## 3. The two directions, and the lifting that connects them

**Forward: form $`\to`$ representation.** One cannot feed a weight-one form
directly into Deligne's cohomological construction, which starts at weight two.
The bridge is the **Deligne–Serre lifting** (the *relèvement*). The key observation
is that multiplying a weight-one form by a weight-one **Eisenstein** series raises
the weight to two: if $`E`$ is modular of weight one and $`f`$ is modular of
weight one, then $`f E`$ is modular of weight two. Choosing $`E`$ with constant
term $`1`$ and with all higher coefficients divisible by $`\ell`$, the product is
congruent to $`f`$ modulo $`\ell`$:

$$f\\,E \\;\equiv\\; f \pmod{\ell}, \qquad \deg(fE) = 2.$$

For $`\ell = 3`$ the series $`E_1(1,\chi_{-3}) = 1 + 6\sum_{n\ge1}\sigma_\chi(n)q^n`$
of [014](014-chi-minus-3-eisenstein.md) is exactly such an $`E`$: its non-constant
coefficients are divisible by $`6`$, hence by $`3`$. In general a weight-one
Eisenstein series attached to a primitive odd character plays the same role, and
FLT proves its existence and its divisor-sum $`q`$-expansion as
`ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd`.

Once a weight-two mod-$`\ell`$ form congruent to $`f`$ is available, Deligne's
construction applies to a genuine weight-two eigenform, and the compatible system
over $`\ell`$ is pieced together. Rankin's bound (§2) then shows the system is
Artin. The abstract step "a residual eigenform is the reduction of a genuine
eigenform of the same weight" is the lifting lemma proper; FLT keeps it separate
(`DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr`) and
specialises it to weight one $`\to`$ weight two
(`DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen`).

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

## 4. Where it sits among the modularity theorems

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

## 5. How FLT uses it: the mod-3 octahedral case

The endgame chain that carries the weight-one input is, in premise direction
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

## 6. The same paper's other result

"Deligne–Serre" names two different things in this project, and they should not
be conflated.

1. The **weight-one/Artin correspondence** of §1, which is the subject of this
   note.
2. **Proposition 2.7** of the same paper, on the integral structure of the
   $`\Gamma_1(N)`$-basis of modular forms. This is the result
   [013-integral-structure-gamma1-basis.md](013-integral-structure-gamma1-basis.md)
   uses (via the trace route C′) to prove the integral structure of
   $`S_k(\Gamma_0(N))`$ for every $`k`$. The provenance is recorded in FLT's own
   documentation; the port's `DeligneSerre271` namespace is this Proposition 2.7,
   not the weight-one correspondence.

The two results sit in the same paper because both come out of the same analytic
study of weight-one forms: the correspondence is the Galois-theoretic output, and
the integrality of the Hecke action is a by-product of the bounded-denominator
analysis that the correspondence needs.

## 7. Oddness: why a weight-one eigenform has odd nebentypus

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

## 8. Lean summary

The mathematics above is the classical theorem. FLT proves it in a strength tuned
to the endgame, in the `DeligneSerre.*` and `LanglandsTunnell.*` namespaces. This
section is the technical summary.

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
  $`\varepsilon(-1) = -1`$ (§7);
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

**The endgame coupling.** The Langlands–Tunnell side is packaged by
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

**Distance from the port.** The weight-one Deligne–Serre family is *on* the
endgame path — it lies in the closure of `FLT.fermatLastTheorem` — but it is
unported. Measured with [../tools/deps/frontier.py](../tools/deps/frontier.py) at
`aa2d8b3`, against the port's 492-node frontier:

| target | cone | new nodes / raw `S_` lines | hops |
|---|---:|---:|---:|
| `exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` | 2,308 | 1,988 / 995,359 | 2 |
| `exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen` | 1,528 | 1,210 / 622,105 | 3 |
| `exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace` | 439 | 421 / 196,678 | 2 |

The port already owns about 309 of the first cone's nodes, almost all on the
modular-curve/function-field side (`ModularCurve` 151, `AlgebraicCurve` 77); the
remaining mass is the unported automorphic block (`AutomorphicForm` 473,
`NumberField` 132, `LanglandsTunnell` 38) plus the weight-one arithmetic itself
(`CuspForm`, `DeligneSerre`, `EisensteinSeries`). The family is a landmark to port
after the arithmetic side packages, not before. The segment assignment and the
full measurement are in
[../studies/flt-non-frey-segments.md](../studies/flt-non-frey-segments.md) §3.4.

## References

* [P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. Éc.
  Norm. Supér. (4) **7** (1974), 507–530](https://www.numdam.org/item/ASENS_1974_4_7_4_507_0/) —
  the theorem of §1 and Proposition 2.7 of §6.
* [P. Deligne, *Formes modulaires et représentations $`\ell`$-adiques*, Sém.
  Bourbaki 1968/69, Exp. 355 (1971), 139–172](https://www.numdam.org/item/SB_1968-1969__11__139_0/) —
  the weight $`\ge 2`$ construction of §2.
* [H. Darmon, *Artin representations attached to forms of weight one*, McGill
  lecture notes 26–27](https://www.math.mcgill.ca/darmon/courses/11-12/nt/notes/lecture26.pdf) —
  a modern exposition of the proof strategy of §3.
* [C. Khare and J.-P. Wintenberger, *Serre's modularity conjecture (I)*, Invent.
  Math. **178** (2009), 485–504](https://link.springer.com/article/10.1007/s00222-009-0205-7) —
  Serre's conjecture of §1/§4.
