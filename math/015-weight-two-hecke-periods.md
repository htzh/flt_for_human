# Finiteness of the weight-two Hecke algebra from periods

FLT proves the Hecke-algebra finiteness statements twice. The general form
`CuspForm.moduleFinite_heckeAlgebra` is the tail of the Eichler–Shimura tower;
the weight-two form `CuspForm.moduleFinite_heckeAlgebra_two` is proved on its
own in a 4,308-line file,
[`S_CuspForm_moduleFinite_heckeAlgebra_two.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean),
which imports only `Mathlib`, three `Definitions/` modules and `P2M.Util`, and
cites no theorem node of the FLT graph (closure 1). This note explains the
mathematics of that file.

It is **not** the Γ₁-basis/trace route of
[013-integral-structure-gamma1-basis.md](013-integral-structure-gamma1-basis.md)
(route C′), and it is not the general Eichler–Shimura package of route A. It is
a self-contained weight-two argument whose integral lattice lives on the
**period/cohomology side**: the Hecke operators act compatibly on ℤ-valued
group cocycles, on ℂ-valued group cocycles, and on cusp forms, and a compatible
triple is determined by its cocycle component. The ℤ-module of cocycles is
finitely generated for trivial reasons (Γ₀(N) is finitely generated), so the
Hecke algebra is finite over ℤ — with no q-expansions, no Sturm bound, no
bounded denominators, and no `HasIntegralStructure`.

FLT is read at the pin `aa2d8b3`; all citations are public URLs at that commit.
Companions: the coverage study
[../studies/hecke-finiteness-coverage.md](../studies/hecke-finiteness-coverage.md)
§2, §5, §7 (the route comparison and why route B is throwaway), and
[013-integral-structure-gamma1-basis.md](013-integral-structure-gamma1-basis.md)
(the C′ route, deliberately not this one).

## 1. The target

`CuspForm.heckeAlgebra N k S` is the ℤ-subalgebra generated inside
`Module.End ℂ (CuspForm (Γ₀ N) k)` by the Hecke operators $`T_\ell`$ for good
primes $`\ell \nmid N`$, $`\ell \notin S`$, and $`U_q`$ for bad primes
$`q \mid N`$, $`q \notin S`$
([`Def_CuspForm_HeckeAlgebra.lean`, L14–L19](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeAlgebra.lean#L14-L19)).
The target is

```lean
theorem CuspForm.moduleFinite_heckeAlgebra_two (N : ℕ) [NeZero N] (S : Set ℕ) :
    Module.Finite ℤ (CuspForm.heckeAlgebra N 2 S)
```

Route B first proves finiteness for the **full** algebra with $`S = \emptyset`$,

```lean
CuspForm.heckeAlgebraIntFull N :=
  Algebra.adjoin ℤ (heckeSet N 2 ∪ heckeUSet N 2)
```

which contains every $`T_\ell`$ ($`\ell \nmid N`$) and every $`U_q`$ ($`q \mid N`$).
The target is a subalgebra of it (`heckeAlgebra_le_heckeAlgebraIntFull`), so
finiteness descends. The whole argument is a single commuting diagram:

```text
S₂(Γ₀(N))  --per-->  addChars_ℂ(Γ₀(N), ℂ)
    |                          |
   T_ℓ                     T_ℓ^cocycle
    v                          v
S₂(Γ₀(N))  --per-->  addChars_ℂ(Γ₀(N), ℂ)
```

together with the fact that the ℤ-lattice `addChars_ℤ(Γ₀(N), ℤ)` inside the
cocycle space is finitely generated.

## 2. Weight-two cusp forms and their periods

Let $`f \in S_2(\Gamma_0(N))`$. Since $`f(\tau)\,d\tau`$ is invariant under
$`\Gamma_0(N)`$ — the weight-two slash relation is exactly the change-of-
variables factor $`d(\gamma\tau) = (c\tau+d)^{-2}\,d\tau`$ — the integral

$$F_f(z) = \int_{i\infty}^{z} f(\tau)\\,d\tau$$

converges (a cusp form decays exponentially at $`\infty`$), satisfies
$`F_f' = f`$, and has the defining property that its difference along
$`\gamma \in \Gamma_0(N)`$ is a constant independent of $`z`$:

$$F_f(\gamma z) - F_f(z) = \int_{z}^{\gamma z} f(\tau)\\,d\tau =: \mathrm{per}_f(\gamma).$$

Independence of $`z`$ is the fundamental theorem of calculus: both
$`F_f \circ \gamma`$ and $`F_f`$ have derivative $`f`$, because
$`(F_f \circ \gamma)' = (F_f' \circ \gamma)\,\gamma' = f|_2\gamma = f`$; two
functions with the same derivative differ by a constant.

Lean formalises precisely this quasi-invariance, without naming the integral:

```lean
def IsEquivariantPrimitive (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ) : Prop :=
  ∀ γ : Γ, ∃ c : ℂ, ∀ z : ℍ, F ((γ : SL(2, ℤ)) • z) - F z = c
```

([L2120–L2121](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean#L2120-L2121)),
with `period hF γ := F (γ • I) - F I`
([L2127–L2128](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean#L2127-L2128)).
The existence theorem constructs such an $`F`$ analytically rather than by
integration: `exists_primitive`
([L2230–L2233](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean#L2230-L2233))
takes a holomorphic function with a period $`h`$ and vanishing at $`i\infty`$,
writes it as a cusp function $`\Phi(q)`$ with $`\Phi(0) = 0`$, divides by
$`q`$, and integrates the resulting power series. It returns a primitive $`G`$
with $`G \to 0`$ at $`i\infty`$. Applied to $`f`$ and to every
$`\Gamma_0(N)`$-translate $`f|_2\delta`$, it yields
`CuspForm.exists_equivariantPrimitive_gamma0`
([L2463–L2469](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean#L2463-L2469)):
a primitive $`F`$ of $`f`$ that tends to $`0`$ at $`i\infty`$, is
$`\Gamma_0(N)`$-equivariant in the above sense, and has a finite limit at every
cusp in the sense that $`\lim_{w \to i\infty} F(\delta w)`$ exists for every
$`\delta \in \mathrm{SL}_2(\mathbb{Z})`$.

Because $`\mathrm{per}_f`$ is additive in the group variable, it is a
**1-cocycle** of $`\Gamma_0(N)`$ with values in the trivial module ℂ:

$$\mathrm{per}_f(\gamma\delta) = \mathrm{per}_f(\gamma) + \mathrm{per}_f(\delta),$$

the telescoping identity $`F(\gamma\delta z) - F(z) = [F(\gamma(\delta z)) -
F(\delta z)] + [F(\delta z) - F(z)]`$
(`IsEquivariantPrimitive.period_mul`, L2135–L2144). The Lean type of cocycles is

```lean
def addChars (R : Type*) [Ring R] (G : Type*) [Group G]
    (M : Type*) [AddCommGroup M] [Module R M] : Submodule R (G → M) where
  carrier := {φ | ∀ γ δ : G, φ (γ * δ) = φ γ + φ δ}
```

([L1695–L1697](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean#L1695-L1697))
— "additive characters", i.e. group homomorphisms written additively. The
period cocycle is `IsEquivariantPrimitive.periodChar : addChars ℂ Γ ℂ`
(L2146–L2147).

Since the primitive is a single-valued function of $`q = e^{2\pi i \tau}`$
(it vanishes at $`i\infty`$ and has no constant term), it is invariant under the
unipotent generator $`\tau \mapsto \tau+1`$, so $`\mathrm{per}_f`$ vanishes
there. Mathematically the same holds for every parabolic element: if $`\gamma`$
fixes a cusp $`p`$, both $`F_f(\gamma z)`$ and $`F_f(z)`$ tend to the same finite
limit as $`z \to p`$ (this is where the finite-limits clause of §2 is used),
and their difference is constant, hence zero. So the period cocycle is
**parabolic**, i.e. it vanishes on elements of trace squared $`4`$; the Lean
defines that submodule as `parabolicChars` (L1797–L1799) and proves it is a
finitely generated ℤ-module. That membership is not formalized in the blob and
is not needed for finiteness: §5 uses the larger module of all cocycles.

## 3. The period map is injective

The period construction is linear in $`f`$:
$`\mathrm{per}_{f+g} = \mathrm{per}_f + \mathrm{per}_g`$ and
$`\mathrm{per}_{cf} = c\,\mathrm{per}_f`$ (`period_add`/`period_smul`,
L2160–L2191). Hence it is a ℂ-linear map

$$\mathrm{per} : S_2(\Gamma_0(N)) \longrightarrow \mathrm{addChars}_\mathbb{C}(\Gamma_0(N), \mathbb{C}),$$

Lean `periodHom` (L3964–L3967). **It is injective** (`periodHom_injective`,
L3973–L3980). Indeed, if $`\mathrm{per}_f = 0`$, then $`F_f`$ is
$`\Gamma_0(N)`$-invariant; it is holomorphic on $`\mathbb{H}`$ and has finite
limits at every cusp (§2); a holomorphic weight-zero modular form bounded at
the cusps is constant (`ModularForm.eq_const_of_weight_zero`, invoked by
`exists_const_of_invariant_of_tendsto`, L3487–L3493); hence $`F_f`$ is constant
and $`f = F_f' = 0`$. The Lean form is
`CuspForm.periodChar_ne_zero_of_ne_zero` (L3551–L3555).

This is the weight-two case of the classical **Eichler–Shimura isomorphism**
$`S_2(\Gamma) \cong H^1_{\mathrm{par}}(\Gamma, \mathbb{C})`$, in its weak form:
route B needs only injectivity, not the identification of the image or
surjectivity. The reason the weak form suffices is exactly the triple-algebra
argument of §6 — the period map only has to be faithful enough to let the third
component of a compatible triple be recovered from the second.

## 4. Hecke operators on periods

The point of the period map is that it intertwines the Hecke action on cusp
forms with a Hecke action on cocycles.

**Group theory.** For a prime $`\ell`$ put

$$\Gamma^0(\ell) = \\{\gamma \in \mathrm{SL}_2(\mathbb{Z}) : \ell \mid \gamma_{01}\\},
\qquad
H_\ell = \Gamma_0(N) \cap \Gamma^0(\ell),$$

Lean `heckeUpperSL`/`heckeUpper` (L2012–L2028). It has finite index, with
coset representatives the classical Hecke matrices

$$\alpha_\infty = \begin{pmatrix}\ell & 0 \\\\ 0 & 1\end{pmatrix}, \qquad
\alpha_j = \begin{pmatrix}1 & j \\\\ 0 & \ell\end{pmatrix}
\quad (j = 0, \dots, \ell-1),$$

Lean `repMat` (L19–L21). These are indexed by `Option (Fin ℓ)`, which has
$`\ell+1`$ elements, and they match the double coset
$`\Gamma_0(N)\,\mathrm{diag}(\ell,1)\,\Gamma_0(N)`$: this is
`HeckeCosetMatch` (L2744–L2747), discharged by `heckeCosetMatch` for
$`\ell \nmid N`$ (L3098–L3104). For a bad prime $`q \mid N`$ the same
construction runs with $`q`$ in place of $`\ell`$, with $`q`$ cosets indexed by
`Fin q` (`heckeUCosetMatch`, L3306–L3313).

The Hecke operator on **cocycles** is restriction followed by corestriction
(transfer) through this correspondence:

$$T_\ell^{\mathrm{coc}} = \mathrm{cor}_{H_\ell}^{\Gamma_0(N)} \circ
\mathrm{res}^{\Gamma_0(N)}_{H_\ell},$$

Lean `heckeOperator` = `(addChars.cores (heckeUpper N ℓ)).comp
(addChars.compHom (heckeConj N ℓ))` (L2087–L2088). The `heckeConj` factor is
the conjugation isomorphism implementing the double-coset correspondence; on
values, for a cocycle $`\phi`$ and $`g \in \Gamma_0(N)`$,

$$(T_\ell^{\mathrm{coc}}\phi)(g) =
\sum_{q \in \Gamma_0(N)/H_\ell}
\phi\bigl(\mathrm{conj}(\mathrm{transferAux}(g,q))\bigr)$$

(`heckeOperator_apply`, L2090–L2095). The operator `cores` is the standard
corestriction for a finite-index subgroup,
$`(\mathrm{cores}\,\psi)(g) = \sum_{q \in G/H} \psi(\mathrm{transferAux}(g,q))`$,
`addChars.cores` (L1868–L1890).

**Equivariance.** If $`F`$ is a primitive for $`f`$, then
$`\sum_j F \circ \alpha_j`$ is a primitive for
$`T_\ell f = \sum_j f|_2\alpha_j`$: the chain rule gives
$`(\sum_j F \circ \alpha_j)' = \sum_j f|_2\alpha_j`$. Its periods are computed
by the telescoping identity

$$\sum_q \Bigl[F(\mathrm{rep}_q(\gamma z)) - F(\mathrm{rep}_q z)\Bigr]
= \sum_q \mathrm{per}_f\bigl(\mathrm{conj}(\mathrm{transferAux}(\gamma,q))\bigr):$$

in each term the two $`F`$-values are moved to a common coset representative and
the remaining difference is a period, and summing over the coset space the shift
$`q \mapsto \gamma^{-1}q`$ is a bijection, so the non-period parts cancel
(`sum_heckeCosetRep_smul_sub`, L2611–L2665). The consequence is

$$\mathrm{per}_{T_\ell f} = T_\ell^{\mathrm{coc}}\\,\mathrm{per}_f$$

(`periodChar_heckeQuotSlashSum` L2695–L2733, `periodChar_hecke_of_match`
L2763–L2776), and the same identity holds for $`U_q`$ (`periodHom_heckeU`,
L4070–L4080). This is the commuting square displayed in §1.

One bookkeeping step is genuinely arithmetic rather than formal: the Lean
definition of the Hecke operator on forms is an explicit sum of slashes by
`repMat`, while the cocycle operator is a group coset sum, and
`heckeSlashSum_eq_heckeQuotSlashSum` (L2751–L2761) shows the two agree after
reindexing by the coset matching. The bad-prime case needs the analogous
`HeckeUCosetMatch` bridge. All of this is coset bookkeeping over
$`\Gamma_0(N)`$, not new analytic input; the only analytic inputs are the
primitive construction of §2 and the weight-zero constancy of §3.

## 5. The integral lattice of cocycles

The integral structure of route B is entirely on the cocycle side.

**(a) The ℤ-cocycles are finitely generated.** Let

$$C_\mathbb{Z} = \mathrm{addChars}_\mathbb{Z}(\Gamma_0(N), \mathbb{Z}),
\qquad
C_\mathbb{C} = \mathrm{addChars}_\mathbb{C}(\Gamma_0(N), \mathbb{C}).$$

A cocycle is a function on the group, so it is determined by its values on a
generating set. Since $`\Gamma_0(N)`$ has finite index in
$`\mathrm{SL}_2(\mathbb{Z}) = \langle S, T\rangle`$, it is finitely generated
(`instGroupFGGamma0`, via `Subgroup.fg_of_index_ne_zero`, L1777–L1778);
choosing a finite generating set $`S`$ embeds $`C_\mathbb{Z}`$ into the finite
product $`\mathbb{Z}^S`$ by evaluation. As ℤ is Noetherian, $`C_\mathbb{Z}`$ is
a finitely generated ℤ-module (`addChars.isNoetherian`, L1750–L1753).
Consequently $`\mathrm{End}_\mathbb{Z}(C_\mathbb{Z})`$ is a finitely generated
ℤ-module (`isNoetherian_end_addChars_int`, L3583–L3585).

**(b) Base change spans.** Coefficient extension $`C_\mathbb{Z} \to
C_\mathbb{C}`$, Lean `ofIntChars` (L3592–L3607), intertwines the Hecke operators
over ℤ and over ℂ (`ofIntChars_heckeOperator`, L3610–L3619), and its image
ℂ-spans $`C_\mathbb{C}`$ (`span_range_ofIntChars`, L3858–L3859). This is the
standard fact that for a finitely generated abelian group $`A`$,
$`\mathrm{Hom}(A, \mathbb{C})`$ is spanned by $`\mathrm{Hom}(A, \mathbb{Z})`$:
the dual-basis argument is `exists_eq_sum_smul_intCast` (L3785–L3808), applied
to the finitely generated group `CharModule G` presented by the cocycle
relations (L3647–L3655, L3698–L3714). A purely linear-algebra warning is
recorded by `gate_line_not_spanned_by_int_points` (L3864–L3898): over an
arbitrary ℂ-vector space the integer points of a line do not span it, so the
spanning here genuinely uses that $`C_\mathbb{Z}`$ is a lattice in
$`C_\mathbb{C}`$ — that is, that base change is surjective, not merely
injective.

## 6. The triple algebra, and finiteness

Route B packages the two Hecke actions and the cusp-form action into one
ℤ-algebra and shows the package is finite. Let

$$H \subseteq \mathrm{End}_\mathbb{Z}(C_\mathbb{Z}) \times
\mathrm{End}_\mathbb{C}(C_\mathbb{C}) \times
\mathrm{End}_\mathbb{C}(S_2(\Gamma_0(N)))$$

be the ℤ-subalgebra generated by the triples
$`(T_\ell^{\mathbb{Z}}, T_\ell^{\mathbb{C}}, T_\ell)`$ and
$`(U_q^{\mathbb{Z}}, U_q^{\mathbb{C}}, U_q)`$: Lean `heckeTripleAlgebraFull`
(L4095–L4096) over `HeckeTripleCarrier` (L4001–L4003). Call a triple
**compatible** if the two intertwining squares of §1 hold:

$$(\mathrm{i})\ \ \mathrm{ofIntChars} \circ T^{\mathbb{Z}} =
T^{\mathbb{C}} \circ \mathrm{ofIntChars},
\qquad
(\mathrm{ii})\ \ \mathrm{per} \circ T = T^{\mathbb{C}} \circ \mathrm{per},$$

Lean `IsCompatibleTriple` (L4011–L4013). Every generator is compatible:
$`(\mathrm{i})`$ by `ofIntChars_heckeOperator`, $`(\mathrm{ii})`$ by the Hecke
equivariance of §4 (`periodHom_hecke`, `periodHom_heckeU`). Compatibility is
closed under sums, products and integer scalars, so every element of $`H`$ is
compatible (`isCompatibleTriple_of_mem_heckeTripleAlgebraFull`, L4102–L4136).

**A compatible triple is determined by its first component.**

- *First determines second.* If two compatible triples have the same first
  component, then their second components agree on the image of
  $`C_\mathbb{Z}`$, which spans $`C_\mathbb{C}`$ by §5(b); hence the second
  components are equal (`snd_eq_of_fst_eq`, L4015–L4020).
- *Second determines third.* If two compatible triples have the same second
  component, then for every $`f`$ the two third components have the same
  periods, and $`\mathrm{per}`$ is injective by §3; hence the third components
  are equal (`trd_eq_of_snd_eq`, L4022–L4026).
- Combined, $`x = y`$ (`eq_of_fst_eq_of_mem_heckeTripleAlgebraFull`,
  L4138–L4145).

Therefore the projection to the first component
$`H \hookrightarrow \mathrm{End}_\mathbb{Z}(C_\mathbb{Z})`$ is injective
(`heckeTripleFstFull_injective`, L4162–L4165), and since the target is a
finitely generated ℤ-module by §5(a), so is $`H`$
(`module_finite_heckeTripleAlgebraFull`, L4169–L4172).

On the other hand the projection to the **third** component is a ℤ-algebra
homomorphism $`H \to \mathrm{End}_\mathbb{C}(S_2(\Gamma_0(N)))`$ whose image on
generators is exactly `heckeSet N 2 ∪ heckeUSet N 2`
(`heckeTripleTrdHom_image_gens`, `heckeTripleTrdHom_image_ugens`), hence whose
image is the full integral Hecke algebra

$$H \twoheadrightarrow \mathrm{heckeAlgebraIntFull}\ N =
\mathrm{Adjoin}_\mathbb{Z}\bigl(T_\ell\ (\ell \nmid N),\ U_q\ (q \mid N)\bigr)$$

(`heckeTripleAlgebraFull_map_trd`, L4185–L4190; the restricted surjection is
`heckeTripleTrdFull_surjective`, L4206–L4213). The image of a finitely generated
module is finitely generated, so `Module.Finite ℤ (heckeAlgebraIntFull N)`
(`module_finite_heckeAlgebraIntFull_unconditional`, L4217–L4221).

Finally, `heckeAlgebra N 2 S` is the subalgebra obtained by discarding the
generators whose prime lies in $`S`$ (`heckeAlgebra_le_heckeAlgebraIntFull`,
L4288–L4293); a subalgebra of a finite ℤ-module is finite. That is the headline
`moduleFinite_heckeAlgebra_two` (L4295–L4301) and the file's exported `solution`
(L4306–L4308).

In one sentence: **the weight-two Hecke algebra is finite over ℤ because it is a
quotient of a ℤ-subalgebra of the endomorphism ring of a finitely generated
ℤ-module (the integral group cocycles), and the period map is faithful enough
to make the quotient map onto the Hecke algebra surjective.**

## 7. Relation to routes A and C′

Route B proves the same statement as the $`k=2`$ specialisation of route A, but
by a different mechanism, with a different hypothesis budget, and with a
different reuse profile.

| | route A (`hasIntegralStructure_of_two_le`) | route C′ (note 013) | route B (this note) |
|---|---|---|---|
| statement | integral structure for all $`k \ge 2`$, then finiteness | integral structure for all $`k`$, then finiteness | weight-two finiteness directly |
| integral lattice | period/cohomology (`coeffH1par`, Eichler–Shimura map, `HeckeEis`) | $`q`$-expansion lattice ($`\Gamma_1`$-basis, bounded denominators, trace) | group cocycles $`\mathrm{addChars}_\mathbb{Z}(\Gamma_0(N), \mathbb{Z})`$ |
| weight range | all $`k \ge 2`$ | all $`k`$ | $`k = 2`$ only |
| inputs | Eichler–Shimura comparison, `ModPForms`, period package | fricke/Hauptmodul analysis, $`\chi_{-3}`$ Eisenstein series, Deligne–Serre Prop. 2.7 | weight-two primitive and its period cocycle, coset bookkeeping |
| measured cone | 657 nodes / 263,720 raw `S_` lines | 53 nodes / 33,719 lines, inside the endgame weight-one branch | 4,308 lines, **closure 1** (self-contained) |
| reusable? | it is the endgame route, for general $`k`$ | yes, shared with the endgame's weight-one branch | no: the $`k=2`$ statement comes free from route A or C′ |

Two mathematical reasons route B does not scale as written. First, its
injectivity argument is the **weight-two** primitive. For $`f \in S_k`$ with
$`k \ne 2`$ the form $`f\,d\tau`$ is not invariant, and the period object must be
replaced by the $`(k-1)`$-fold Eichler integral, taking values in a coefficient
system $`\mathrm{Sym}^{k-2}`$; that is route A's period package, not a two-line
change. Second, route B never proves `HasIntegralStructure`: it establishes that
the Hecke **action** is integral (the algebra is a quotient of a subalgebra of
$`\mathrm{End}_\mathbb{Z}`$ of an integral lattice), but not that
$`S_2(\Gamma_0(N))`$ has a basis with integral $`q`$-expansions. Finiteness of
the Hecke algebra is weaker than the integral-structure statement, and it is the
integral-structure statement that route A and C′ deliver and that the endgame
consumes at general weight.

So route B is cheap but not reusable: a self-contained blob that buys the
$`k=2`$ statement for the 44 downstream consumers before a general theorem
lands, and is then deleted rather than superseded in place. See
[../studies/hecke-finiteness-coverage.md](../studies/hecke-finiteness-coverage.md)
§2 and §5.

## 8. Declarations and pointers

All Lean line numbers below refer to
[`S_CuspForm_moduleFinite_heckeAlgebra_two.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean)
at the pin `aa2d8b3`.

| mathematics | Lean declarations |
|---|---|
| primitive / quasi-invariance | `IsEquivariantPrimitive` L2120, `period` L2127, `period_mul` L2135 |
| existence of the primitive | `exists_primitive` L2230, `CuspForm.exists_equivariantPrimitive_gamma0` L2463 |
| period cocycle; parabolic | `IsEquivariantPrimitive.periodChar` L2146, `parabolicChars` L1797 |
| period map and injectivity | `periodHom` L3964, `periodHom_injective` L3973, `periodChar_ne_zero_of_ne_zero` L3551 |
| Hecke cosets | `heckeUpper` L2028, `repMat` L19, `HeckeCosetMatch` L2744, `heckeCosetMatch` L3098, `heckeUCosetMatch` L3306 |
| Hecke operator on cocycles | `addChars.cores` L1868, `heckeOperator` L2087, `ofIntChars_heckeOperator` L3610 |
| Hecke equivariance of periods | `sum_heckeCosetRep_smul_sub` L2611, `periodChar_heckeQuotSlashSum` L2695, `periodHom_hecke` L3982, `periodHom_heckeU` L4070 |
| cocycle lattice finite | `addChars.isNoetherian` L1750, `isNoetherian_end_addChars_int` L3583 |
| base change spans | `exists_eq_sum_smul_intCast` L3785, `span_range_ofIntChars` L3858 |
| triple algebra | `IsCompatibleTriple` L4011, `snd_eq_of_fst_eq` L4015, `trd_eq_of_snd_eq` L4022, `heckeTripleAlgebraFull` L4095 |
| finiteness | `module_finite_heckeTripleAlgebraFull` L4169, `heckeTripleAlgebraFull_map_trd` L4185, `module_finite_heckeAlgebraIntFull_unconditional` L4217 |
| the target | `moduleFinite_heckeAlgebra_two` L4295, `solution` L4306 |

Pointers:

- The blob:
  [`S_CuspForm_moduleFinite_heckeAlgebra_two.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean)
  (4,308 lines, closure 1). The exported theorem node is
  [`Thm_CuspForm_moduleFinite_heckeAlgebra_two.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_moduleFinite_heckeAlgebra_two.lean),
  glossed "Integral weight-two Hecke algebra is finite over ℤ".
- The general route A input:
  [`S_CuspForm_hasIntegralStructure_of_two_le.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_hasIntegralStructure_of_two_le.lean).
- The route comparison and the throwaway verdict:
  [../studies/hecke-finiteness-coverage.md](../studies/hecke-finiteness-coverage.md)
  §2, §5, §7.
- The C′ route (the one the port actually takes):
  [013-integral-structure-gamma1-basis.md](013-integral-structure-gamma1-basis.md),
  [../studies/route-c-prime-scout.md](../studies/route-c-prime-scout.md).
- Standard background: G. Shimura, *Introduction to the Arithmetic Theory of
  Automorphic Functions*, Ch. III–IV (periods of cusp forms and Eichler–Shimura);
  S. Lang, *Introduction to Modular Forms*, Ch. V; Deligne–Serre, *Formes
  modulaires de poids 1*.
