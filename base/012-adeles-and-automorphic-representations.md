# Adeles, automorphic representations, and the adelic dictionary

Twelfth of the `base/` notes. [002](002-modular-forms-basics.md) built the
classical modular-forms side ($`\Gamma_0(N)`$, $`q`$-expansions, Hecke
operators on $`S_2(\Gamma_0(N))`$), [010](010-finite-fields-frobenius-and-point-counts.md)
the residual Galois representations and their characteristic polynomials, and
[011](011-deformations-hecke-algebras-and-r-equals-t.md) the deformation and
Hecke-algebra layer. This note is the **adelic** layer those three are usually
translated into: the ring of adeles, $`\mathrm{GL}_2`$ over it, automorphic
representations and their local factors, the dictionary that turns a classical
cusp form into an adelic function, the Hecke operators on both sides, Hecke
characters and Grössencharacters, and local newvectors with their conductor.
It is the language notes 002's projective side eventually feeds, and it is where
the modularity statement of the FLT proof is most naturally phrased.

Math first: §§1–8 are the theory, §9 says where the proof uses it, and §10
gathers the Lean encoding with the key-point table. There is no `pymath` demo
for this topic; the worked examples are two dictionary theorems quoted in §6
and §8. One piece of the standard theory is *not* formalized and is flagged as
such in §4: the restricted-tensor-product decomposition of a global automorphic
representation into local ones.

Line-number citations point at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib
citations point at tag **v4.33.0**. Both are rendered GitHub links.

## 1. The adele ring as a restricted product

Let $`K`$ be a number field with ring of integers $`\mathcal{O}`$, and let
$`v`$ run over its places. Each place has a completion and a ring of integers
inside it:

- a finite place $`v`$ (a nonzero prime ideal) gives the $`v`$-adic completion
  $`K_v`$ with ring of integers $`\mathcal{O}_v`$, the closure of
  $`\mathcal{O}`$ in $`K_v`$;
- an infinite place gives $`K_v = \mathbb{R}`$ or $`\mathbb{C}`$.

The ordinary product $`\prod_v K_v`$ is not locally compact, so one keeps only
the tuples that are integral almost everywhere. The **adele ring** is

$$\mathbb{A}_K \\;=\\; \Bigl\\{ (x_v)_v \in \prod_v K_v :
  x_v \in \mathcal{O}_v \text{ for almost all } v \Bigr\\},$$

with the **restricted product** topology: a basis is given by products of open
sets in finitely many coordinates and $`\mathcal{O}_v`$ in all the others. This
is the smallest modification of the product that is locally compact, and it
retains $`K`$: the diagonal embedding

$$K \longrightarrow \mathbb{A}_K, \qquad x \longmapsto (x)_v$$

has discrete image, with quotient compact. Splitting off the finitely many
infinite places gives the standard shape

$$\mathbb{A}_K \\;=\\; \prod_{v \mid \infty} K_v \\;\times\\; \mathbb{A}_K^{\mathrm{fin}},
  \qquad \mathbb{A}_K^{\mathrm{fin}} \\;=\\;
  \prod_{v \nmid \infty}{}^{\\!\\!\prime}\\, K_v ,$$

where the prime marks the restricted product with respect to the $`\mathcal{O}_v`$
(the notation $`\prod'`$ is not standard LaTeX; mathlib writes the restriction
as a separate product type, §10). Because each $`\mathcal{O}_v`$ is compact and
open and almost all coordinates are constrained, $`\mathbb{A}_K`$ is locally
compact, and it is a ring by coordinatewise operations — the reason the
construction is made here, before any group structure.

## 2. The ideles and the idele class group

The units of the adele ring are the **ideles**:

$$\mathbb{A}_K^\times \\;=\\; \Bigl\\{ (x_v)_v \in \prod_v K_v^\times :
  x_v \in \mathcal{O}_v^\times \text{ for almost all } v \Bigr\\},$$

again with the restricted product topology (not the subspace topology). The
diagonal $`K^\times`$ sits inside as a discrete subgroup, and the **idele class
group** is the quotient

$$C_K \\;=\\; K^\times \backslash \mathbb{A}_K^\times .$$

Two structural facts make $`C_K`$ the right home for the characters of §8.

**The product formula gives a norm.** For the normalized absolute values
$`|\cdot|_v`$ one has $`\prod_v |x|_v = 1`$ for every $`x \in K^\times`$, so
the adelic absolute value

$$|\cdot|_{\mathbb{A}} \\;:\\; C_K \longrightarrow \mathbb{R}_{\gt 0},
  \qquad (x_v) \longmapsto \prod_v |x_v|_v$$

is a well-defined continuous homomorphism.

**Its kernel is compact.** The subgroup $`C_K^0 = \ker |\cdot|_{\mathbb{A}}`$ of
idele classes of norm $`1`$ is compact, and the norm identifies
$`C_K \cong C_K^0 \times \mathbb{R}_{\gt 0}`$ (up to a finite index issue
governed by the roots of unity). This compactness is the adelic form of the
finiteness of the class number together with Dirichlet's unit theorem: what is
finite at the level of ideals becomes compact at the level of ideles.

A **character of the idele class group**, or idele-class character, is thus a
continuous homomorphism $`\chi : \mathbb{A}_K^\times \to \mathbb{C}^\times`$
with $`\chi(x) = 1`$ for every $`x \in K^\times`$ on the diagonal. The code's
`IsIdeleClassChar` is exactly this last condition, and every Hecke character of
§8 is such a $`\chi`$.

## 3. $`\mathrm{GL}_2`$ over the adeles, and the compact-open $`K_0(N)`$

Write

$$G(\mathbb{A}) \\;=\\; \mathrm{GL}_2(\mathbb{A}_K)$$

for the adele-valued points. It is a locally compact group, totally disconnected
at the finite places, and it carries the extra structures the theory needs: a
maximal compact subgroup and a basis of compact-open subgroups around the
identity.

**Maximal compact.** At a finite place $`v`$ the group $`\mathrm{GL}_2(K_v)`$
has the compact open subgroup $`\mathrm{GL}_2(\mathcal{O}_v)`$; at an infinite
place it has the usual maximal compact (the orthogonal group up to the centre
over $`\mathbb{R}`$, the unitary group over $`\mathbb{C}`$). Their product
$`K = \prod_v K_v`$ is a maximal compact subgroup of $`G(\mathbb{A})`$, and the
"maximal compact" of the code, `adelicMaximalCompact`, is the simultaneous
version: finite part in the integral matrices and each archimedean component a
row isometry.

**Congruence subgroups.** For an ideal $`N \subseteq \mathcal{O}`$ the classical
$`\Gamma_0(N)`$ has two adelic counterparts, obtained by imposing a congruence
condition on the finite part only:

$$K_0(N) \\;=\\; \\{\\, g \in K^{\mathrm{fin}} :
  g \bmod N \text{ is upper triangular} \\,\\},$$

and $`K_1(N)`$, which requires $`g \equiv 1`$ modulo $`N`$. Both are compact
open. The condition is imposed placewise, which is the content of

$$K_0(N) \\;=\\; \prod_{v \nmid \infty} K_{0,v}(N)$$

for the local groups $`K_{0,v}(N)`$ cut out by the same congruence at $`v`$.
This local factorization is what makes the level a *product of local levels*, and
it is what the code records: `finiteLevelZero`/`finiteLevelOne` are the
congruence subgroups of the finite adeles, `levelZero`/`levelOne` lift them
along the projection $`\mathrm{GL}_2(\mathbb{A}_K) \to \mathrm{GL}_2(\mathbb{A}_K^{\mathrm{fin}})`$
so that the infinite places are unconstrained, and `localLevelOne` is a single
local factor.

**Strong approximation.** The double coset space
$`G(K) \backslash G(\mathbb{A}) / K_0(N) Z(\mathbb{A})`$ has finitely many
components, each a copy of $`\Gamma_0(N) \backslash \mathbb{H}`$. This is why
the level-$`N`$ classical world and the $`K_0(N)`$-invariant adelic world are
the same thing, and it is the mechanism behind the dictionary of §5.

## 4. Automorphic representations, and the local-global picture

An **automorphic form** on $`G`$ is a function

$$\varphi \\;:\\; G(K) \backslash G(\mathbb{A}) \longrightarrow \mathbb{C}$$

that is left $`G(K)`$-invariant by definition, right $`K`$-finite, finite under
the centre, and of moderate growth; it is **cuspidal** when its constant term
along the unipotent radical vanishes. The group $`G(\mathbb{A})`$ acts on the
space of such functions by right translation, $`(g \cdot \varphi)(x) = \varphi(x g)`$,
and this is the representation that matters:

- an **automorphic representation** is an irreducible constituent of that
  right-regular representation (a subquotient of the space of automorphic
  forms);
- a **cuspidal automorphic representation** is one realized in the cuspidal
  subspace;
- **admissibility** says that each local group $`G(K_v)`$ acts smoothly and
  that its fixed vectors under a compact open subgroup are finite-dimensional.

The central structural theorem is the **tensor product decomposition**. For an
irreducible automorphic $`\pi`$,

$$\pi \\;\cong\\; \bigotimes_v{}^{\\!\\!\prime}\\, \pi_v,$$

a restricted tensor product of irreducible admissible representations $`\pi_v`$
of the local groups $`G(K_v)`$: the restriction is with respect to a chosen
spherical vector at almost every place, and for all but finitely many $`v`$ the
local representation $`\pi_v`$ is **unramified** — it has a nonzero
$`\mathrm{GL}_2(\mathcal{O}_v)`$-fixed vector, and the spherical Hecke algebra
of the pair $`(G(K_v), \mathrm{GL}_2(\mathcal{O}_v))`$ acts on that line by a
character, the Satake parameter. Consequently the whole global object is
determined by finitely many local data (the ramified $`\pi_v`$, the central
character) together with a Hecke eigenvalue at every unramified place. That is
the shape in which modularity and level lowering are stated.

**One caveat about the code.** The formalization does *not* appear to contain
this tensor product decomposition. What it contains instead is the raw material
for it: the space of adelic functions with its right-translation action
(`AdelicFnCarrier`), the subrepresentation generated by a single function
(`AdelicSpan`, the smallest $`G(\mathbb{A})`$-stable subspace containing it),
the submodules of vectors fixed by a compact open subgroup (`fixedSubmodule`),
and the condition of being an eigenfunction for the local Hecke operators
(`IsHeckeEigenfunctionOf`, §6). A reader looking for the decomposition itself
should read §4 as the mathematics behind those declarations, not as a citation.

## 5. The classical ↔ adelic dictionary

The dictionary is a translation, form by form. A classical cusp form
$`f \in S_k(\Gamma_0(N))`$ becomes the adelic function $`\varphi_f`$ defined by

$$\varphi_f(\gamma g_\infty k) \\;=\\; (f \mid_k g_\infty)(i),
  \qquad \gamma \in G(\mathbb{Q}), \quad k \in K_0(N),$$

where $`\mid_k`$ is the weight-$`k`$ slash action and $`i \in \mathbb{H}`$ is the
base point. Strong approximation (§3) makes this well-defined, and the two
properties it encodes are exactly the two symmetries of an adelic function:

| classical | adelic |
|---|---|
| the modular transformation law | left invariance under $`G(\mathbb{Q})`$ |
| invariance under $`\Gamma_0(N)`$ | right invariance under $`K_0(N)`$ |
| the value $`f(z)`$ | evaluation at the archimedean component $`g_\infty`$ |

The code writes those clauses directly. The $`\Gamma_0(N)`$ version is
`IsAdelicLiftOf` and the $`\Gamma_1(N)`$ version is `IsAdelicLiftOfGamma1`;
each is a conjunction of three statements: left invariance under global
$`\mathrm{GL}_2(\mathbb{Q})`$, right invariance under the finite level
subgroup, and an archimedean clause identifying the value of $`\varphi`$ with a
slash operator applied to the classical form. The third clause is stated for
matrices whose finite part is trivial and whose archimedean part has positive
determinant, which is precisely the set on which the classical value is read off.

Two further entries in the dictionary are used constantly:

- **Nebentypus.** A classical character $`\varepsilon`$ modulo $`N`$ becomes the
  **central character** of the adelic lift, and a central character of an
  automorphic representation is a Hecke character. This is the content of the
  theorem quoted in §8: a form with nebentypus $`\varepsilon`$ has an adelic lift
  whose central scalar action is by a finite-order Hecke character $`\omega`$
  with $`\omega`$ agreeing with $`\varepsilon`$ at every good prime.
- **Weight.** The weight is an archimedean datum, not a global one: it fixes the
  transformation of $`\varphi`$ under the maximal compact at the infinite places,
  while the level $`N`$ is purely a finite-place datum. This separation is the
  practical advantage of the adelic language, and it is why a level change (§7)
  can be discussed one prime at a time.

## 6. Hecke operators and the eigenvalue dictionary

Classically, $`T_\ell`$ for $`\ell \nmid N`$ and $`U_\ell`$ for $`\ell \mid N`$
act on $`S_k(\Gamma_0(N))`$ by correspondences and commute; a normalized
eigenform is determined by its eigenvalue sequence $`a_\ell`$, which is also its
$`q`$-coefficient sequence.

Adelically the same operators are double coset operators. For a compact open
subgroup $`U \subseteq G(\mathbb{A})`$ the **Hecke algebra** is the algebra of
compactly supported $`U`$-bi-invariant functions, multiplied by convolution, and
a double coset $`U g U`$ acts on the $`U`$-fixed vectors of any smooth
representation. At an unramified place the relevant double coset is the one of
the diagonal matrix with entries $`1`$ and a uniformizer, and the resulting
operator is the local Hecke operator at that place. The identification with the
classical theory is:

$$T_\ell \text{ on } S_k(\Gamma_0(N)) \quad \longleftrightarrow \quad
  \text{the Hecke operator at } \ell \text{ on the } K_0(N)\text{-fixed vectors},$$

and the eigenvalues agree, because both are computed on the same double coset.
This is the *eigenvalue dictionary*: the classical $`a_\ell = \lambda`$ is the
adelic eigenvalue of the local operator.

The code has both halves.

- The abstract Hecke operator is `HeckeOperator`, a linear map on the fixed
  points of a compact open subgroup $`U`$ associated with an element $`g`$ and
  the double coset $`UgU`$; `HeckeOperator_toFun` is its action. The local
  spherical algebra is `heckeSubmodule` and its abbreviation `HeckeAlgebra`:
  the submodule of functions on the group that are $`U`$-bi-invariant and
  finitely supported on cosets.
- The global Hecke algebra acting on the modular side is the polynomial algebra
  `HeckeAlg`, one generator `heckeGen ℓ` per prime, with `eigenIdeal` recording
  the eigenvalue system; a Hecke module is a type with a
  `Module HeckeAlg` instance, which is how the Hecke action on $`J_0(N)`$ is
  stated.
- The adelic eigenfunction condition is `IsHeckeEigenfunctionOf`: a function
  fixed by the level right-translation subgroup `levelRT` and an eigenvector of
  the Hecke operator at every unramified $`v`$, with the eigen-data packaged as
  a `HeckeEigensystem` — a level ideal together with two families of eigenvalues
  $`a`$ and $`b`$. The eigenvalue $`b`$ at a place is normalized by the central
  character: it is the residue-field cardinality times the value of the central
  character on the uniformizer idele `uniformizerIdele`.
- The bridge is a theorem quoted verbatim in §10: the classical
  nebentypus-twisted $`q`$-coefficient recursion for $`F`$ at $`\ell`$ is
  equivalent to the adelic eigenvalue equation

$$\sum_{i} \Psi\bigl(h \cdot \mathrm{padicToAdelic}_\ell(\rho_i)^{-1}\bigr)
  \\;=\\; \lambda \\, \Psi(h),$$

where the $`\rho_i`$ run through the $`\ell + 1`$ representatives of the relevant
double coset ($`\ell`$ of them the upper unitriangular translations and one the
diagonal). This single theorem is the dictionary for Hecke eigenvalues made
explicit.

## 7. Local newvectors, conductor, and level

The local theory behind the level is the theory of newvectors. Fix a prime
$`p`$ and an irreducible admissible representation $`V`$ of
$`\mathrm{GL}_2(\mathbb{Q}_p)`$ with a central character. The congruence
subgroups $`K_1(p^c)`$ decrease with $`c`$, so the spaces of $`K_1(p^c)`$-fixed
vectors increase; there is a least $`c`$ for which the space is nonzero, and a
nonzero vector there is a **newvector**. The **conductor** of $`V`$ is
$`p^{c}`$:

$$c(V) \\;=\\; \min\\{\\, c \ge 0 : V^{K_1(p^c)} \neq 0 \\,\\},$$

with $`c(V) = 0`$ exactly when $`V`$ is unramified and the newvector is the
spherical vector. This is the local invariant that globalizes: the conductor of
an automorphic representation is the product of the local conductors, and for a
classical form it is the level, so a level change is a statement about one local
factor at a time.

The code states this invariant, its uniqueness, and the surrounding notions:

- the fixed vectors are the submodule `fixedSubmodule U V` of vectors killed by
  every element of a subgroup $`U`$;
- `HasNewvectorConductor V c` says that the $`K_1(p^c)`$-fixed space is nonzero
  and that every strictly smaller level has zero fixed space — the defining
  property of the minimal level — and `hasNewvectorConductor_unique` shows such
  a $`c`$ is unique;
- `IsCentralCharacterRep V ω` says $`V`$ acts by the character $`ω`$ through the
  central scalars, with `centralCharacterRep_unique` giving uniqueness of $`ω`$
  when $`V`$ is nonzero;
- `IsIrreducibleGLRep V` is irreducibility in the representation-theoretic
  sense used locally: no proper nontrivial invariant subspace;
- `HasFiniteLevelFixed V` is the admissibility condition that every level has a
  finite-dimensional fixed space.

On the character side the same idea gives the **conductor of a character**:
`IsUnramified μ` says a local character is trivial on the units of valuation
$`1`$; `higherUnits n` is the group of units congruent to $`1`$ to precision
$`n`$; and `valChar` is the basic unramified character
$`u \mapsto s^{v(u)}`$ built from the valuation. Globally the corresponding
notion is `AdmitsModulus χ 𝔣`: the Hecke character $`χ`$ is trivial on the
ideles that are $`1`$ modulo the ideal $`𝔣`$ and units at the other places,
with `idealMultiplicity v 𝔣` the exponent of $`v`$ in $`𝔣`$. So a modulus is to a
Hecke character what a level is to an automorphic representation.

## 8. Hecke characters, Grössencharacters, and the cyclotomic character

A **Hecke character** of $`K`$ — classically a **Grössencharacter** — is a
continuous homomorphism

$$\chi \\;:\\; C_K \\;=\\; K^\times \backslash \mathbb{A}_K^\times
  \longrightarrow \mathbb{C}^\times,$$

equivalently a continuous character of $`\mathbb{A}_K^\times`$ trivial on the
diagonal $`K^\times`$ (§2). Two special classes matter:

- **Unitary** characters, with $`|\chi(u)| = 1`$ for all $`u`$; the code's
  `IsUnitaryChar`.
- **Finite-order** characters, with finite image. These are the ones class field
  theory sees: they are exactly the characters of finite abelian extensions of
  $`K`$, and the classical special case is a Dirichlet character. In the code
  `IsFiniteOrderHeckeChar` bundles the three properties — trivial on the
  diagonal, continuous, and of finite order — while `idealMultiplicity` and
  `AdmitsModulus` record the modulus.

The archimedean part of a Grössencharacter is its **infinity type**: a
character of $`(\mathbb{R}_{\gt0})`$ or $`\mathbb{C}^\times`$ of the form
$`z \mapsto z^{-m} \bar z^{-n}`$, which is where the weight of a modular form
enters; the finite part is unramified at almost all places. So a Hecke character
of weight $`(m,n)`$ is a finite-order character times a fixed archimedean
factor.

**The cyclotomic character as an idele-class character.** Let
$`\chi_\ell : G_{\mathbb{Q}} \to \mathbb{Z}_\ell^\times`$ be the cyclotomic
character, the action on the $`\ell`$-power roots of unity. By the reciprocity
map of global class field theory the abelianized Galois group is the idele class
group, so $`\chi_\ell`$ corresponds to an idele-class character of $`\mathbb{Q}`$
whose local component at $`p \neq \ell`$ is unramified and takes a uniformizer
to $`p`$, i.e. the inverse of the $`p`$-adic absolute value. Its role in FLT is
the determinant of the Galois representation on torsion: [007 §2](007-weil-pairing.md)
derives $`\det \rho = \chi_\ell`$ from the Weil pairing, and
[010 §5](010-finite-fields-frobenius-and-point-counts.md) reads the constant term
of the Frobenius characteristic polynomial as this character's value. The
code's local avatar of this unramified local character is `valChar`,
constructed from `unitValuation`. What the code does *not* contain, as far as
this note could verify, is an explicit idele-class character of $`\mathbb{Q}`$
named as the cyclotomic character; the Galois-side object is
`modularCyclotomicCharacter` ([001 §7](001-field-extensions-and-galois-basics.md)).

## 9. Where the layer is cashed in

Four uses, in increasing specificity to the FLT proof.

**Modularity is a statement about automorphic representations.** The Frey
curve's residual representation is attached to a cusp form
([010 §5](010-finite-fields-frobenius-and-point-counts.md)), and the modern
form of that attachment is that the Galois representation is a constituent of an
automorphic representation. The local factors of §4 are what make the statement
checkable prime by prime.

**Level lowering is local.** Replacing the level $`N`$ by a smaller one is done
one prime at a time, and in the adelic picture that is the statement that a
local factor $`\pi_v`$ at a ramified prime is replaced by a less ramified one;
the classical formulation (Ribet's theorem, [math/008](../math/008-ribet-level-lowering.md))
is the product of those local moves.

**The nebentypus is a Hecke character.** The classical Dirichlet character of a
form with nebentypus is realized as the central character of its adelic lift,
and the central character of an automorphic representation is a finite-order
Hecke character of §8. This is the theorem quoted in §10.

**Hecke eigenvalues agree.** The classical $`q`$-coefficient recursion and the
adelic Hecke eigenvalue equation are the same statement, which is what lets the
Hecke-algebra computation of [011](011-deformations-hecke-algebras-and-r-equals-t.md)
be run on the adelic side; the theorem of §6 is the bridge.

## 10. How the code says all this

**The adele ring is mathlib's, not FLT's.** The definition is a product of the
infinite part with the finite part, and the finite part is the restricted
product over the height-one spectrum, written with mathlib's own restricted
product notation:

```lean
def AdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] := InfiniteAdeleRing K × FiniteAdeleRing R K
```
```lean
def FiniteAdeleRing : Type _ :=
  Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]
```

([NumberField/AdeleRing.lean, line 47, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/NumberField/AdeleRing.lean#L47),
[RingTheory/DedekindDomain/FiniteAdeleRing.lean, line 94, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean#L94)),
with `InfiniteAdeleRing K := (v : InfinitePlace K) → v.Completion`
([NumberField/InfiniteAdeleRing.lean, line 52, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/NumberField/InfiniteAdeleRing.lean#L52))
and the notation $`\mathbb{A}[K]`$ for `AdeleRing (𝓞 K) K` ([line 58](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/NumberField/AdeleRing.lean#L58)).
The local factors are `HeightOneSpectrum R`
([DedekindDomain/Ideal/Lemmas.lean, line 493, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean#L493))
and the completion together with its integers
([AdicValuation.lean, lines 600 and 804, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean#L600-L804)).

**$`\mathrm{GL}_2`$ over the adeles is one abbreviation.** FLT's group is

```lean
abbrev AdelicGL2 : Type _ :=
  Matrix.GeneralLinearGroup (Fin 2) (AdeleRing R K)
```

([Def_AutomorphicForm_AdelicLsXi.lean, lines 12–13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AdelicLsXi.lean#L12-L13)),
and the maximal compact is the subgroup whose finite part is integral and whose
archimedean components are row isometries, `adelicMaximalCompact`
([Def_AutomorphicForm_AdelicMaximalCompact.lean, line 19](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean#L19)),
which is compact by `isCompact_adelicMaximalCompact`
([line 176](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean#L176))
and closed by `isClosed_adelicMaximalCompact`
([line 114](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean#L114)).

**Levels are congruence subgroups, lifted along the finite projection.** The
finite-level subgroups and their adelic lifts are

```lean
def finiteLevelZero : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) where
  carrier := {g | IsLevelZeroMatrix R K N (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) ∧
    IsLevelZeroMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)}
```
```lean
def finiteLevelOne : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) where
  carrier := {g | IsLevelOneMatrix R K N (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) ∧
    IsLevelOneMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)}
```
```lean
def levelOne : Subgroup (GL (Fin 2) (AdeleRing R K)) := (finiteLevelOne R K N).comap (glFin R K)
```

([Def_NumberField_AdelicLevel.lean, lines 410, 418 and 589](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_NumberField_AdelicLevel.lean#L410-L589)).
Note the shape of the lift: `levelOne` is the *comap* of `finiteLevelOne` along
the projection `glFin` to the finite adeles
([line 194](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_NumberField_AdelicLevel.lean#L194)),
which is how "the level condition is imposed at the finite places only" is
encoded. The local factors are `localLevelOne`
([Def_AdelicDock_LocalEmbedding.lean, line 178](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AdelicDock_LocalEmbedding.lean#L178))
and, over $`\mathbb{Q}`$, the local subgroups `padicK0`/`padicK1`
([Def_LocalNewvector_CongruenceSubgroupK1.lean, lines 158 and 161](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_CongruenceSubgroupK1.lean#L158-L161)),
with the general local congruence groups `congruenceK0`/`congruenceK1`
([lines 15 and 55](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_CongruenceSubgroupK1.lean#L15-L55)).

**Local data is assembled into adelic data with explicit embeddings.** The
`AdelicDock` family puts a local group into the finite adeles with a single
nontrivial coordinate and then into the adeles:

```lean
def localEmbed : GL (Fin 2) (v.adicCompletion K) →* GL (Fin 2) (FiniteAdeleRing R K) where
```
```lean
def padicToAdelic : GL (Fin 2) ℚ_[p] →* GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  (finEmbed (𝓞 ℚ) ℚ).comp (padicToFinAdelic p)
```

([Def_AdelicDock_LocalEmbedding.lean, line 97](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AdelicDock_LocalEmbedding.lean#L97),
[line 254](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AdelicDock_LocalEmbedding.lean#L254)),
with the level comparison `finEmbed_mem_levelOne_iff`
([line 170](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AdelicDock_LocalEmbedding.lean#L170))
and the rational level ideal `ratLevel N = Ideal.span {N}`
([line 303](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AdelicDock_LocalEmbedding.lean#L303)).

**Automorphy is two symmetries plus a cuspidality condition.** The invariance
and central-character structure is

```lean
structure IsLsXiFunction (φ : AdelicGL2 R K → ℂ) : Prop where
  left_invariant : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 R K),
    φ (globalPoints R K γ * g) = φ g
  central_transform : ∀ (z : Z) (g : AdelicGL2 R K),
    φ (centralScalar R K (z : (AdeleRing R K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g
```

([Def_AutomorphicForm_AdelicLsXi.lean, lines 33–38](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AdelicLsXi.lean#L33-L38)),
an idele-class character is triviality on the diagonal
([line 21](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AdelicLsXi.lean#L21)),
automorphy at a carrier is `IsAutomorphicFnAt` and cuspidality is
`IsCuspAutomorphicFnAt`
([Def_AutomorphicForm_AutomorphicFnAt.lean, lines 34 and 38](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AutomorphicFnAt.lean#L34-L38)),
and the vanishing of the constant term is `IsCuspidalFn`
([Def_AutomorphicForm_ConstantTerm.lean, line 58](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_ConstantTerm.lean#L58)),
built from `unipotentGL2` ([line 17](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_ConstantTerm.lean#L17))
and `constantTerm` ([line 47](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_ConstantTerm.lean#L47)).
The dictionary of §5 is written out in full, as three clauses:

```lean
def IsAdelicLiftOfGamma1 (g : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) : Prop :=
  (∀ (γ : GL (Fin 2) ℚ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      φ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * x) = φ x) ∧
    (∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel M),
      ∀ x, φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = φ x) ∧
    ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
          φ h = ((⇑g) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I
```

([Def_CuspForm_AdelicLiftGamma1.lean, lines 14–24](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_AdelicLiftGamma1.lean#L14-L24)),
with the $`\Gamma_0(N)`$ version `IsAdelicLiftOf`
([Def_CuspForm_AdelicLift.lean, lines 14–24](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_AdelicLift.lean#L14-L24))
and the classical nebentypus predicate `HasNebentypus`
([Def_CuspForm_PrimitiveFormGamma1.lean, line 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_PrimitiveFormGamma1.lean#L13)).

**The subrepresentation generated by one function** is the adelic span, which
is where irreducibility would be tested:

```lean
def AdelicSpanSubmodule (φ : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicFnCarrier F) :=
  Submodule.span ℂ {ψ | ∃ g : AdelicGL2 (𝓞 F) F, ψ = g • AdelicFnCarrier.mk φ}
```

([Def_LocalNewvector_AdelicSpanCarrier.lean, line 66](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_AdelicSpanCarrier.lean#L66)),
on the carrier of adelic functions `AdelicFnCarrier`
([line 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_AdelicSpanCarrier.lean#L13))
with the right-translation action
([line 43](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_AdelicSpanCarrier.lean#L43))
and the subrepresentation structure `AdelicSpan` ([line 82](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_AdelicSpanCarrier.lean#L82)).

**Newvectors.** Fixed vectors, the conductor, uniqueness, the central character
and irreducibility are

```lean
def fixedSubmodule {G : Type*} [Group G] (U : Subgroup G) (V : Type*) [AddCommGroup V]
    [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V] : Submodule ℂ V where
  carrier := {v | ∀ g ∈ U, g • v = v}
```
```lean
def HasNewvectorConductor (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ V]
    (c : ℕ) : Prop :=
  fixedSubmodule (padicK1 p c) V ≠ ⊥ ∧ ∀ m < c, fixedSubmodule (padicK1 p m) V = ⊥
```

([Def_LocalNewvector_ConductorDatum.lean, lines 11 and 88](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_ConductorDatum.lean#L11-L88)),
with `hasNewvectorConductor_unique` ([line 93](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_ConductorDatum.lean#L93)),
`IsCentralCharacterRep` ([line 67](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_ConductorDatum.lean#L67)),
`IsIrreducibleGLRep` ([line 102](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_ConductorDatum.lean#L102))
and `HasFiniteLevelFixed` ([line 108](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_ConductorDatum.lean#L108)).
The character conductor lives in its own file: `IsUnramified`
([Def_LocalNewvector_CharConductor.lean, line 11](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_CharConductor.lean#L11)),
`unitValuation` ([line 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_CharConductor.lean#L16)),
`valChar` ([line 26](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_CharConductor.lean#L26))
and `higherUnits` ([line 62](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_CharConductor.lean#L62)).

**Hecke operators and the eigenfunction condition.**

```lean
noncomputable def HeckeOperator : fixedPoints V A →ₗ[R] fixedPoints U A where
```
```lean
abbrev HeckeAlg : Type := MvPolynomial Nat.Primes ℤ
```
```lean
abbrev HeckeAlgebra := heckeSubmodule U R₀
```

([Def_AbstractHeckeOperator.lean, line 136](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AbstractHeckeOperator.lean#L136),
[Def_HeckeGalois_EichlerShimura.lean, line 14](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean#L14),
[Def_LocalLanglands_HeckePair.lean, line 63](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalLanglands_HeckePair.lean#L63)),
with `heckeSubmodule` ([line 57](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalLanglands_HeckePair.lean#L57)),
`heckeGen` ([Def_HeckeGalois_EichlerShimura.lean, line 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean#L16))
and `eigenIdeal` ([line 30](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean#L30)).
The adelic eigenfunction package is

```lean
structure HeckeEigensystem (F : Type*) [Field F] [NumberField F]
    (R : Type*) [CommRing R] where
  level : Ideal (𝓞 F)
  level_ne_bot : level ≠ ⊥
  a : HeightOneSpectrum (𝓞 F) → R
  b : HeightOneSpectrum (𝓞 F) → R
```
```lean
def IsHeckeEigenfunctionOf (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (Φ : HeckeEigensystem F ℂ) : Prop :=
```

([Def_AutomorphicForm_HeckeEigensystem.lean, lines 9–18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_HeckeEigensystem.lean#L9-L18),
[Def_AutomorphicForm_HeckeEigenfunction.lean, line 42](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_HeckeEigenfunction.lean#L42)),
with the level subgroup `levelRT` ([line 38](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_HeckeEigenfunction.lean#L38)),
the uniformizer idele ([line 31](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_HeckeEigenfunction.lean#L31))
and the carrier pins ([Def_AutomorphicForm_CarrierPins.lean, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_CarrierPins.lean#L10)).

**The two dictionary theorems.** The eigenvalue dictionary of §6 and the
nebentypus-as-central-character statement of §5 are both theorems, and they are
the closest thing this topic has to a worked example:

```lean
theorem CuspForm.HasNebentypus.qCoeff_hecke_eq_of_isAdelicLiftOfGamma1_of_sum_apply_padicToAdelic_eq
    {N : ℕ} [NeZero N] {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 2}
    (hε : CuspForm.HasNebentypus ε F)
    (Ψ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (hΨ : CuspForm.IsAdelicLiftOfGamma1 F Ψ)
```
```lean
theorem CuspForm.HasNebentypus.exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hε : CuspForm.HasNebentypus ε h)
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    ∃ ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ,
      HeckeCharacter.IsFiniteOrderHeckeChar ℚ ω ∧
      HeckeCharacter.AdmitsModulus ℚ ω (AdelicDock.ratLevel M) ∧
```

([Thm_CuspForm_HasNebentypus_qCoeff_hecke_eq…lean, line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_HasNebentypus_qCoeff_hecke_eq_of_isAdelicLiftOfGamma1_of_sum_apply_padicToAdelic_eq.lean#L9),
[Thm_CuspForm_HasNebentypus_exists_isFiniteOrderHeckeChar…lean, line 14](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_HasNebentypus_exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1.lean#L14)).
The first concludes the classical recursion
$`\mathrm{qCoeff}\,F(\ell n) + \varepsilon(\ell)\ell^{k-1}\mathrm{qCoeff}\,F(n/\ell) = \varepsilon(\ell)\lambda\,\mathrm{qCoeff}\,F(n)`$
from the adelic eigenvalue equation; the second produces the finite-order Hecke
character $`\omega`$ that
realizes the central character, with modulus the rational level ideal and value
$`\varepsilon(\ell)`$ at every good prime $`\ell`$.

### Key point → declaration map

| Mathematics | Lean declaration | Location |
|---|---|---|
| the adele ring as infinite × finite | `AdeleRing` | [NumberField/AdeleRing.lean 47](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/NumberField/AdeleRing.lean#L47) |
| the restricted product of completions | `FiniteAdeleRing`, `Πʳ` | [FiniteAdeleRing.lean 94](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean#L94), [RestrictedProduct/Basic.lean 85](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean#L85) |
| the archimedean product | `InfiniteAdeleRing` | [InfiniteAdeleRing.lean 52](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/NumberField/InfiniteAdeleRing.lean#L52) |
| places, completions, integers | `HeightOneSpectrum`, `adicCompletion`, `adicCompletionIntegers` | [Ideal/Lemmas.lean 493](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean#L493), [AdicValuation.lean 600, 804](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean#L600-L804) |
| $`\mathrm{GL}_2(\mathbb{A})`$ | `AdelicGL2` | [AdelicLsXi 12–13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AdelicLsXi.lean#L12-L13) |
| maximal compact | `adelicMaximalCompact` | [AdelicMaximalCompact 19](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean#L19) |
| $`K_0(N)`$, $`K_1(N)`$ over the finite adeles | `finiteLevelZero`, `finiteLevelOne` | [AdelicLevel 410, 418](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_NumberField_AdelicLevel.lean#L410-L418) |
| the adelic level (finite places only) | `levelZero`, `levelOne`, `glFin` | [AdelicLevel 587, 589, 194](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_NumberField_AdelicLevel.lean#L587-L589) |
| the local factor of a level | `localLevelOne`, `padicK0`, `padicK1` | [AdelicDock 178](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AdelicDock_LocalEmbedding.lean#L178), [K1 158, 161](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_CongruenceSubgroupK1.lean#L158-L161) |
| local datum into the adeles | `localEmbed`, `finEmbed`, `padicToAdelic` | [AdelicDock 97, 145, 254](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AdelicDock_LocalEmbedding.lean#L97-L254) |
| local level inside the adelic level | `finEmbed_mem_levelOne_iff` | [AdelicDock 170](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AdelicDock_LocalEmbedding.lean#L170) |
| automorphy: left invariance + central character | `IsLsXiFunction` | [AdelicLsXi 33–38](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AdelicLsXi.lean#L33-L38) |
| idele-class character | `IsIdeleClassChar`, `IsUnitaryChar` | [AdelicLsXi 21, 24](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AdelicLsXi.lean#L21-L24) |
| cuspidality (vanishing constant term) | `IsCuspidalFn`, `constantTerm`, `unipotentGL2` | [ConstantTerm 17, 47, 58](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_ConstantTerm.lean#L17-L58) |
| classical cusp form as an adelic function | `IsAdelicLiftOf`, `IsAdelicLiftOfGamma1` | [AdelicLift 14–24](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_AdelicLift.lean#L14-L24), [AdelicLiftGamma1 14–24](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_AdelicLiftGamma1.lean#L14-L24) |
| nebentypus | `HasNebentypus` | [PrimitiveFormGamma1 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_PrimitiveFormGamma1.lean#L13) |
| the subrepresentation generated by a function | `AdelicFnCarrier`, `AdelicSpan` | [AdelicSpanCarrier 13, 66, 82](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_AdelicSpanCarrier.lean#L13-L82) |
| fixed vectors, newvector conductor | `fixedSubmodule`, `HasNewvectorConductor` | [ConductorDatum 11, 88, 93](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_ConductorDatum.lean#L11-L93) |
| central character, local irreducibility, admissibility | `IsCentralCharacterRep`, `IsIrreducibleGLRep`, `HasFiniteLevelFixed` | [ConductorDatum 67, 102, 108](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_ConductorDatum.lean#L67-L108) |
| unramified character, valuation character, higher units | `IsUnramified`, `valChar`, `higherUnits` | [CharConductor 11, 26, 62](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_CharConductor.lean#L11-L62) |
| finite-order Hecke character, its modulus | `IsFiniteOrderHeckeChar`, `AdmitsModulus`, `idealMultiplicity` | [HeckeCharacter_FiniteOrder 13, 18, 21](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeCharacter_FiniteOrder.lean#L13-L21) |
| the Hecke operator on fixed points | `HeckeOperator`, `HeckeOperator_toFun` | [AbstractHeckeOperator 102, 136](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AbstractHeckeOperator.lean#L102-L136) |
| spherical Hecke algebra of a pair | `heckeSubmodule`, `HeckeAlgebra`, `integralSubgroup` | [HeckePair 57, 63](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalLanglands_HeckePair.lean#L57-L63), [LocalHeckeInstance 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalLanglands_LocalHeckeInstance.lean#L13) |
| the global Hecke algebra on the modular side | `HeckeAlg`, `heckeGen`, `eigenIdeal` | [EichlerShimura 14, 16, 30](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean#L14-L30) |
| Hecke eigen-data and eigenfunction | `HeckeEigensystem`, `IsHeckeEigenfunctionOf` | [HeckeEigensystem 9–18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_HeckeEigensystem.lean#L9-L18), [HeckeEigenfunction 42](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_HeckeEigenfunction.lean#L42) |
| classical eigenvalue = adelic eigenvalue | `qCoeff_hecke_eq_of_isAdelicLiftOfGamma1_of_sum_apply_padicToAdelic_eq` | [Thm 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_HasNebentypus_qCoeff_hecke_eq_of_isAdelicLiftOfGamma1_of_sum_apply_padicToAdelic_eq.lean#L9) |
| nebentypus as a finite-order Hecke character | `exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1` | [Thm 14](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_HasNebentypus_exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1.lean#L14) |
| Haar measure on the adelic group | `adelicAddHaar`, `adelicGLHaar`, `adeleBorel` | [AdelicHaar 146, 189, 132](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_NumberField_AdelicHaar.lean#L132-L189) |
| congruence subgroups of $`\mathrm{SL}_2(\mathbb{Z})`$ | `Gamma0`, `Gamma1` | [CongruenceSubgroups 79, 131](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L79-L131) |

## 11. Links

File-level pointers; the anchored citations are inline above.

FLT sources at the pinned sha `aa2d8b3`:

- [Def_AutomorphicForm_AdelicLsXi.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AdelicLsXi.lean) — `AdelicGL2`, `globalPoints`, `centralScalar`, `IsIdeleClassChar`, `IsLsXiFunction`
- [Def_AutomorphicForm_AdelicMaximalCompact.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean) — `adelicMaximalCompact`
- [Def_NumberField_AdelicLevel.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_NumberField_AdelicLevel.lean) — `finiteLevelZero`, `finiteLevelOne`, `levelZero`, `levelOne`, `glFin`
- [Def_AdelicDock_LocalEmbedding.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AdelicDock_LocalEmbedding.lean) — `localEmbed`, `finEmbed`, `padicToAdelic`, `localLevelOne`, `ratLevel`
- [Def_NumberField_AdelicHaar.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_NumberField_AdelicHaar.lean) — `adeleBorel`, `adelicAddHaar`, `adelicGLHaar`
- [Def_AutomorphicForm_AutomorphicFnAt.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AutomorphicFnAt.lean) — `IsAutomorphicFnAt`, `IsCuspAutomorphicFnAt`
- [Def_AutomorphicForm_ConstantTerm.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_ConstantTerm.lean) — `unipotentGL2`, `constantTerm`, `IsCuspidalFn`
- [Def_AutomorphicForm_CarrierPins.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_CarrierPins.lean) — `CarrierPins`
- [Def_CuspForm_AdelicLift.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_AdelicLift.lean) and [Def_CuspForm_AdelicLiftGamma1.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_AdelicLiftGamma1.lean) — the classical ↔ adelic dictionary
- [Def_CuspForm_PrimitiveFormGamma1.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_PrimitiveFormGamma1.lean) — `HasNebentypus`
- [Def_LocalNewvector_ConductorDatum.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_ConductorDatum.lean) — `fixedSubmodule`, `HasNewvectorConductor`, `IsIrreducibleGLRep`
- [Def_LocalNewvector_CongruenceSubgroupK1.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_CongruenceSubgroupK1.lean) — `congruenceK0`, `congruenceK1`, `padicK0`, `padicK1`
- [Def_LocalNewvector_CharConductor.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_CharConductor.lean) — `IsUnramified`, `unitValuation`, `valChar`, `higherUnits`
- [Def_LocalNewvector_AdelicSpanCarrier.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalNewvector_AdelicSpanCarrier.lean) — `AdelicFnCarrier`, `AdelicSpan`
- [Def_AutomorphicForm_HeckeEigensystem.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_HeckeEigensystem.lean) and [Def_AutomorphicForm_HeckeEigenfunction.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_HeckeEigenfunction.lean) — `HeckeEigensystem`, `IsHeckeEigenfunctionOf`
- [Def_AbstractHeckeOperator.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AbstractHeckeOperator.lean) — `HeckeOperator`
- [Def_LocalLanglands_HeckePair.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalLanglands_HeckePair.lean) and [Def_LocalLanglands_LocalHeckeInstance.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LocalLanglands_LocalHeckeInstance.lean) — `heckeSubmodule`, `HeckeAlgebra`, `integralSubgroup`
- [Def_HeckeGalois_EichlerShimura.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean) — `HeckeAlg`, `heckeGen`, `eigenIdeal`
- [Def_HeckeCharacter_FiniteOrder.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeCharacter_FiniteOrder.lean) — `IsFiniteOrderHeckeChar`, `AdmitsModulus`, `idealMultiplicity`
- [Def_RepTheory_GL2CongruenceSubgroup.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_RepTheory_GL2CongruenceSubgroup.lean) — `gl2CongruenceSubgroup`
- [Thm_CuspForm_HasNebentypus_qCoeff_hecke_eq_of_isAdelicLiftOfGamma1_of_sum_apply_padicToAdelic_eq.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_HasNebentypus_qCoeff_hecke_eq_of_isAdelicLiftOfGamma1_of_sum_apply_padicToAdelic_eq.lean)
- [Thm_CuspForm_HasNebentypus_exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_HasNebentypus_exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1.lean)

Mathlib at tag `v4.33.0`:

- [`AdeleRing` and the notation $`\mathbb{A}[K]`$](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/NumberField/AdeleRing.lean) — [47](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/NumberField/AdeleRing.lean#L47), [58](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/NumberField/AdeleRing.lean#L58)
- [`FiniteAdeleRing`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean) — [94](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean#L94)
- [`InfiniteAdeleRing`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/NumberField/InfiniteAdeleRing.lean) — [52](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/NumberField/InfiniteAdeleRing.lean#L52)
- [The restricted product](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean) — [85](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean#L85)
- [`HeightOneSpectrum`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean) — [493](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean#L493)
- [`adicCompletion` and `adicCompletionIntegers`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean) — [600](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean#L600), [804](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean#L804)
- [`Gamma0` and `Gamma1`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean) — [79](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L79), [131](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L131)

Companion notes:

- [002 — Modular forms basics](002-modular-forms-basics.md) — the classical side this note translates
- [011 — Deformations, Hecke algebras, and $`R = T`$](011-deformations-hecke-algebras-and-r-equals-t.md) — the Hecke-algebra ring that the adelic Hecke operators feed
- [010 — Finite fields, Frobenius, and point counts](010-finite-fields-frobenius-and-point-counts.md) — the Galois side, and the characteristic polynomial a Hecke eigenvalue is matched against
- [007 — The Weil pairing](007-weil-pairing.md) — the determinant and the cyclotomic character
- [001 — Field extensions, Galois groups, and Galois actions](001-field-extensions-and-galois-basics.md) — the Galois vocabulary, and the action of a group on a module
- [math/008](../math/008-ribet-level-lowering.md) — level lowering in the classical language; [math/009](../math/009-hecke-jacobian-commute.md) — the Hecke action on $`J_0(N)`$
