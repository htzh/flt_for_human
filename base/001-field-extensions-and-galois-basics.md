# Field extensions, Galois groups, and Galois actions

First of the `base/` notes, which document the foundational layers the FLT proof
rests on: the mathematics that every statement in `Definitions/` is written
against. Later notes assume this one.

The mathematics comes first: §§1–6 are the field theory and Galois theory —
extensions and their adjectives, the Galois group and what it acts on,
decomposition and inertia, the Galois action on modules, and the Galois
correspondence. §7 gathers how the code encodes all of it, with the key-point
table; §8 lists the reading traps of that encoding. §6 is new relative to the
first version of this note: it folds in the module-action language
(`IsGaloisStable`, the fixed/cofixed dichotomy) that the FLT predicates
`GaloisRepIsIrreducible` and `HasGaloisStableCofixedLine` are built from — no
extra background is needed for it beyond §1–§5 and elementary module theory.

The running example is the one object all the companion notes share,
$`\bar{\mathbb{Q}}`$ and its automorphism group. Companion notes in
[`../math/`](../math/): 003 and 004 (the predicates `GaloisRepIsIrreducible`
and `HasGaloisStableCofixedLine`), 005 (why the $`p`$-torsion of the Frey curve
is $`\mathbb{F}_p^2`$), 006 (fixed or cofixed, where inertia decides).

Line-number citations point at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib
citations point at tag **v4.33.0**. Both are rendered GitHub links.

## 1. The field theory the proof lives in

Everything in the proof happens inside one field: the algebraic closure
$`\bar{\mathbb{Q}}`$ of $`\mathbb{Q}`$. Three mathematical facts about it shape
every statement in the development.

**It is algebraic and algebraically closed.** Every element is a root of a
nonzero polynomial over $`\mathbb{Q}`$, and every nonconstant polynomial over it
has a root. Those are the two properties that define an algebraic closure, and
they are all the proof ever uses: a curve with coefficients in $`\mathbb{Q}`$
has all of its $`n`$-torsion defined over any such field (the torsion points are
roots of polynomials with rational coefficients), and for every $`n`$ the field
contains $`n`$ distinct $`n`$-th roots of unity.

**Automorphisms are the group.** The absolute Galois group
$`\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})`$ is the group of field
automorphisms of $`\bar{\mathbb{Q}}`$ fixing $`\mathbb{Q}`$ pointwise. It is not
an ad-hoc object with a separate construction: it is defined as those
automorphisms, with composition as the group law.

**That is where the isogeny question goes.** "There is a degree-$`p`$ rational
isogeny out of $`E_P`$" becomes "the absolute Galois group admits a stable line
in $`E_P[p]`$": the kernel of a rational isogeny is a subgroup defined over
$`\mathbb{Q}`$, and over $`\mathbb{Q}`$ the points of $`E_P[p]`$ are exactly the
ones on which the whole group acts, so a rational subgroup is a Galois-stable
one. This is the sentence the rest of the series decodes, and §5 gives the
module version of it.

## 2. Extensions and their adjectives

A **field extension** $`K/S`$ is, mathematically, a field $`K`$ together with an
embedding $`S \hookrightarrow K`$ — the data of a base field inside a bigger one.
Two extensions are the same when the embeddings agree, and a **tower**
$`R \to S \to K`$ is the situation of two successive embeddings, in which the
element $`K`$ gets its $`R`$-structure through $`S`$: the triangle commutes, so
"$`K`$ as an $`R`$-algebra" and "$`K`$ as an $`S`$-algebra" are compatible, not
two competing structures.

The adjectives, each a property of the embedding:

| property | mathematics |
|---|---|
| **algebraic** | every element of $`K`$ is a root of a nonzero polynomial over $`S`$ |
| **algebraically closed** | every nonconstant polynomial over $`K`$ has a root in $`K`$ |
| **algebraic closure of $`S`$** | algebraic over $`S`$ *and* algebraically closed |
| **separable** | the minimal polynomials over $`S`$ have distinct roots |
| **normal** | the minimal polynomials over $`S`$ split completely in $`K`$ |
| **Galois** | normal *and* separable |

Two of these do real work in the FLT setting.

**Characteristic zero makes everything separable.** Over a field of
characteristic $`0`$, every algebraic extension is separable. So for
$`\bar{\mathbb{Q}}/\mathbb{Q}`$ separability is free, and the interesting
adjective is normality — which an algebraic closure has by construction, since
the minimal polynomial of an element already has a root there and algebraic
closure forces all of its roots to be there as well.

**An algebraic closure is not unique, only unique up to isomorphism.** That is
why "let $`\bar{\mathbb{Q}}`$ be the algebraic closure" is not a definition of a
canonical field; it is a choice of a type satisfying two properties, and every
theorem used in the proof must hold for *any* field with those properties. This
is the first of the encoding points of §7, and it is a mathematical point, not a
formal one: the classical statement is that algebraic closures are unique up to
$`S`$-isomorphism.

## 3. The Galois group, and what it acts on

For an extension $`K/S`$, the **Galois group** is the group of $`S`$-algebra
automorphisms of $`K`$,

$$\mathrm{Gal}(K/S) \\;=\\; \\{\\, \sigma : K \to K \ \text{field automorphism}
  \ \text{with } \sigma|_S = \mathrm{id} \\,\\},$$

with composition as the group law. For a finite Galois extension its order is
the degree, $`\#\mathrm{Gal}(K/S) = [K : S]`$; for the infinite absolute group
that counting statement is replaced by the profinite structure of §6.

**The action on a curve.** Let $`W`$ be a curve whose defining coefficients all
lie in $`S`$ — so $`S`$ is its *field of definition*. An automorphism $`\sigma`$
of $`K`$ fixing $`S`$ fixes those coefficients, hence maps $`W`$ to itself, and
applying it to coordinates gives an action on the point group,

$$\sigma \cdot (x, y) \\;=\\; (\sigma x, \sigma y), \qquad \sigma \cdot O = O .$$

Because the formulas for the group law also have their coefficients in $`S`$,
this action is by *group* automorphisms: $`\sigma(P + Q) = \sigma P + \sigma Q`$,
and $`\sigma(nP) = n(\sigma P)`$ for every $`n`$. By contrast, an automorphism
that moved the coefficients would carry $`W`$ to a different curve $`W^\sigma`$
and give no action on $`W`$ itself; that is why the automorphisms are taken over
the field of definition $`S`$, and not over the larger field $`K`$. Two
consequences are used constantly:

- the $`n`$-torsion is stable under the action, because "$`nP = O`$" is again a
  condition with coefficients in $`S`$;
- in the FLT applications the curve has rational coefficients, so the acting
  group is the absolute Galois group of $`\mathbb{Q}`$ and $`S = \mathbb{Q}`$.

**Representation language.** Once the action on $`E[n] \cong (\mathbb{Z}/n)^2`$
is fixed, choosing a basis turns it into a group homomorphism
$`\mathrm{Gal}(K/S) \to \mathrm{GL}_2(\mathbb{Z}/n)`$ — the mod-$`n`$ Galois
representation — and two invariants of that homomorphism are used repeatedly:
its **determinant**, which for the torsion of an elliptic curve is the
cyclotomic character (the action on $`n`$-th roots of unity, as
[007 §2](007-weil-pairing.md) derives from the Weil pairing), and its
**oddness**: complex conjugation, the order-two element cut out by a real place,
acts with determinant $`-1`$. §5 states the fixed-or-cofixed alternative for a
line in that two-dimensional module; [math/003](../math/003-galois-rep-irreducible-in-english.md)
and [math/004](../math/004-irreducible-and-cofixed-line.md) are the notes that
consume it.

## 4. Decomposition, inertia, and unramifiedness

Local questions at a prime are handled by two subgroups of the absolute group,
attached to a **place**. A place of the big field $`L`$ is a valuation ring
$`A \subseteq L`$ with fraction field $`L`$ — the algebraic stand-in for a point
of the curve, with its maximal ideal playing the role of "functions vanishing
there" and its residue field $`A/\mathfrak{m}_A`$ the field of values.

- The **decomposition group** of $`A`$ is its stabilizer under the action of
  $`\mathrm{Gal}(L/K)`$: the automorphisms that carry the place to itself.
- The **inertia subgroup** is the kernel of the resulting action on the residue
  field: those automorphisms that preserve $`A`$ and act trivially modulo
  $`\mathfrak{m}_A`$.
- A representation is **unramified** at a prime $`q`$ when every inertia element
  of every place above $`q`$ acts trivially on it.

That is the entire local vocabulary of the proof. In particular, the local
questions at $`q`$ are answered by these subgroups *over $`\mathbb{Q}`$*: the
relevant local group is the inflation of a decomposition group at a place of
$`\bar{\mathbb{Q}}`$, not a group over $`\mathbb{Q}_q`$, and
[math/006](../math/006-fixed-or-cofixed-and-inertia.md) is where that
observation is used.

## 5. Galois actions on modules

The action of §3 is used through its linear-algebra shadow, and this section
fixes that language. Let $`M`$ be a $`\mathbb{Z}/n`$-module (in the application,
$`E[n]`$) on which $`\mathrm{Gal}(K/S)`$ acts, compatibly with the scalars: the
action and the $`\mathbb{Z}`$-action commute, so $`M`$ is a module for the group
ring.

**What the typeclasses mean, in mathematics.** An action is a map
$`G \times M \to M`$; that it is *additive* in the module variable and
multiplicative in the group are separate requirements; and that the group action
commutes with the scalar action is a third. In the code these are `SMul`,
`DistribMulAction` and `SMulCommClass`, and the combination is what makes it
legitimate to speak of a $`\mathbb{Z}/n[G]`$-module.

**Stable submodules.** A submodule $`N \subseteq M`$ is **Galois-stable** when
$`\sigma(N) \subseteq N`$ for every $`\sigma \in G`$ (equivalently, since
$`G`$ is a group, $`\sigma(N) = N`$). Stability is exactly what a subgroup
defined over the base field looks like on torsion. The representation is
**irreducible** when the only stable submodules are $`0`$ and $`M`$ — the FLT
predicate `GaloisRepIsIrreducible` says precisely this, together with $`M \neq 0`$.
The mathematical content of the isogeny question is: an irreducible
two-dimensional representation has no stable line.

**Fixed, and cofixed.** For a stable submodule $`N`$ there are two ways an
element of $`G`$ can act on it, and the proof only ever sees these two:

- $`N`$ is **fixed** when $`\sigma x = x`$ for every $`\sigma`$ and $`x \in N`$;
- $`N`$ is **cofixed** when $`\sigma x - x \in N`$ for every $`\sigma`$ and
  $`x`$ — the action is trivial *on the quotient* $`M/N`$, not on $`N`$ itself.

The second is the more subtle one: elementwise it is not an action on $`N`$ but
a statement one level up, and it is stated elementwise in the code for exactly
that reason (there is no quotient to build). For a line in a two-dimensional
irreducible representation the two cases exhaust the possibilities, and that is
the dichotomy of [math/006](../math/006-fixed-or-cofixed-and-inertia.md): if
$`\sigma`$ preserves a line in a two-dimensional module, the induced map on the
quotient is again one-dimensional, so the line is either fixed or cofixed.

**The representation as a homomorphism.** "The Galois action" of §3 is the same
data viewed as a monoid homomorphism

$$G \\;\longrightarrow\\; \mathrm{Aut}_{\mathbb{Z}/n}(M),$$

into the module automorphisms of $`M`$ — the form in which determinants, traces
and characteristic polynomials of Frobenius (the subject of
[010](010-finite-fields-frobenius-and-point-counts.md)) are taken. The
endomorphism-ring version, `Module.toModuleEnd`, is the same construction when
the target has no inverse.

## 6. The Galois correspondence

The correspondence between subgroups and intermediate fields is the backbone of
classical Galois theory, in two versions.

**Finite.** For a finite Galois extension $`K/S`$, a subgroup
$`H \le \mathrm{Gal}(K/S)`$ has a **fixed field** $`K^H`$, and an intermediate field
$`S \subseteq F \subseteq K`$ has a **fixing subgroup**
$`\mathrm{Gal}(K/F) \le \mathrm{Gal}(K/S)`$. The two operations are inverse
order-reversing bijections, and normality of $`F/S`$ corresponds to the
subgroup being normal.

**Infinite.** For $`\bar{\mathbb{Q}}/\mathbb{Q}`$ the bijection must be with
*closed* subgroups for the Krull topology, since the group is profinite. The
moral for the FLT side is worth stating because it is easy to get wrong: "the
representation is continuous" is *not* formalized as a topological condition on
a map out of the absolute Galois group. Where the proof needs finiteness, it
produces an explicit finite intermediate field and works there. That is also how
"an element fixed by a subgroup" is used: as the definition of a field of
invariants, e.g. to descend scalars from $`\bar{\mathbb{Q}}_p`$ to a ring of
integers.

## 7. How the code says all this

Mathlib states the whole theory for *rings*, not fields, and encodes the
embedding of §2 as an algebra structure. Three encoding choices matter.

**An extension is an `Algebra` instance.** "$`K/S`$ is a field extension"
becomes a ring homomorphism $`S \to K`$ together with its compatibility, and a
tower becomes a third `Algebra` instance plus a compatibility hypothesis:

```lean
-- Def_FLTPrelim_GaloisRep.lean, lines 21–23
variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]
```

([Def_FLTPrelim_GaloisRep.lean, lines 21–23](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean#L21-L23)).
Read the binders as the triangle of §2: `R` is the coefficient ring of the
curve, `S` and `K` are `R`-algebras, `K` is an `S`-algebra, and
`IsScalarTower R S K` is the commuting triangle. The generality is inherited
rather than needed: `R` is a ring because the curve's base change and group law
live there, and the local-at-$`p`$ automorphisms are built as their own function
`localAut`
([Def_GaloisRep_LocalFlatClasses.lean, line 14](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_LocalFlatClasses.lean#L14))
rather than by instantiating this tower. Every concrete instantiation in the
repository pins `R = S = ℚ` and `K = AlgebraicClosure ℚ`.

**An algebraic closure is a property, not a field.** The ambient field is

```lean
AlgebraicClosure ℚ
```

with the hypothesis `IsAlgClosure ℚ (AlgebraicClosure ℚ)`, whose fields are
exactly the two of §1 (`IsAlgClosed K` and `Algebra.IsAlgebraic R K`,
[FieldTheory/IsAlgClosed/Basic.lean, lines 62 and 264, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/IsAlgClosed/Basic.lean#L62-L264)).
The adjectives of §2 are `Prop`-valued classes — `Algebra.IsAlgebraic`,
`IsAlgClosed`, `Normal`, `Algebra.IsSeparable`
([RingTheory/Algebraic/Defs.lean, line 68](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Algebraic/Defs.lean#L68),
[FieldTheory/Normal/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Normal/Basic.lean),
[FieldTheory/Separable.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Separable.lean)) —
and mathlib derives normal and separable for free from an algebraic closure,
the second under `[CharZero R]`

```lean
instance (priority := 100) IsAlgClosure.normal (R K : Type*) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] : Normal R K where
  toIsAlgebraic := IsAlgClosure.isAlgebraic
  splits' _ := (IsAlgClosure.isAlgClosed R).splits _
```

([lines 275–282, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/IsAlgClosed/Basic.lean#L275-L282)),
which is §2's "characteristic zero makes everything separable" as an instance.

**The group is a type.** There is no `GaloisGroup` structure: the group is the
type of **algebra equivalences**,

```lean
notation:50 A " ≃ₐ[" R "] " A' => AlgEquiv R A A'
```

([Algebra/Algebra/Equiv.lean, lines 31 and 42, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Algebra/Equiv.lean#L31-L42)),
an element of which is a bijective `S`-algebra homomorphism, with group
structure from composition. So the absolute Galois group of $`\mathbb{Q}`$
appears in the sources as `AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`. There
is also a notation `Gal(L/K)` for it
([FieldTheory/Galois/Notation.lean, line 35, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Notation.lean#L35)),
which FLT almost never uses. `IsGalois` is the class of §2's last row,

```lean
class IsGalois : Prop where
  [to_isSeparable : Algebra.IsSeparable F E]
  [to_normal : Normal F E]
```

([FieldTheory/Galois/Basic.lean, lines 54–59, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean#L54-L59)),
and the instance that $`\bar{\mathbb{Q}}/\mathbb{Q}`$ is Galois needs
characteristic zero ([lines 590–591](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean#L590-L591)). FLT spells it out once, with all
typeclass arguments pinned, as
[Def_FieldTheory_RatAlgClosureGalois.lean, lines 5–7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FieldTheory_RatAlgClosureGalois.lean#L5-L7).

**The action.** An `S`-algebra homomorphism acts on points by `Point.map`, a
homomorphism of groups
([Affine/Point.lean, lines 793–799, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean#L793-L799)),
and FLT packages the action of the group on the $`n`$-torsion as three ordinary
constructions — no representation theory until the last line:

```lean
noncomputable instance instSMulAlgEquiv : SMul (K ≃ₐ[S] K) (W'⁄K).Point :=
  ⟨fun σ P => Point.map σ.toAlgHom P⟩
```
```lean
noncomputable def galoisRep (W' : Affine R) (n : ℕ) :
    (K ≃ₐ[S] K) →*
      (Submodule.torsionBy ℤ (W'⁄K).Point n) ≃ₗ[ZMod n] (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  DistribMulAction.toModuleAut (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)
```

([Def_FLTPrelim_GaloisRep.lean, line 25](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean#L25),
[Def_FreyPackage_GaloisRep.lean, line 18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FreyPackage_GaloisRep.lean#L18)).
The three pieces are §5's three requirements: an `SMul` from `Point.map`, a
`DistribMulAction` from the functoriality of `Point.map`, and the
$`\mathbb{Z}/n`$-module structure on torsion

```lean
noncomputable instance instModuleZModTorsionBy (n : ℕ) :
    Module (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  AddCommGroup.zmodModule fun x => by
    rw [← Nat.cast_smul_eq_nsmul ℤ n x]
    exact Submodule.smul_torsionBy _ x
```

([lines 60–65](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean#L60-L65)).
The representation is then `DistribMulAction.toModuleAut`
([Algebra/Module/Equiv/Basic.lean, line 201, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/Equiv/Basic.lean#L201)),
and its endomorphism-ring sibling is `Module.toModuleEnd`.

**Stability and the dichotomy.** §5's definitions are two FLT predicates:

```lean
def IsGaloisStable {n : ℕ}
    (N : Submodule (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)) : Prop :=
  ∀ (σ : K ≃ₐ[S] K), ∀ x ∈ N, σ • x ∈ N
```
```lean
def GaloisRepIsIrreducible (W' : Affine R) (n : ℕ) : Prop :=
  Nontrivial (Submodule.torsionBy ℤ (W'⁄K).Point n) ∧
    ∀ N : Submodule (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n),
      IsGaloisStable S N → N = ⊥ ∨ N = ⊤
```

([Def_FLTPrelim_GaloisRep.lean, lines 68–77](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean#L68-L77))
for the stable-submodule condition and irreducibility, and

```lean
def HasGaloisStableCofixedLine (W' : Affine R) (n : ℕ) : Prop :=
  ∃ N : Submodule (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n),
    IsGaloisStable S N ∧ N ≠ ⊥ ∧ N ≠ ⊤ ∧
      ∀ σ : K ≃ₐ[S] K, ∀ x : Submodule.torsionBy ℤ (W'⁄K).Point n, σ • x - x ∈ N
```

([Def_FLTPrelim_CofixedLine.lean, lines 15–19](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_CofixedLine.lean#L15-L19))
for cofixedness. Note how §5's remark is encoded: cofixedness is an elementwise
condition `σ • x - x ∈ N`, with no quotient group constructed, and the
`N ≠ ⊥`, `N ≠ ⊤` clauses record that the line is proper and nonzero. The
`SMulCommClass` instance that makes these two actions live together is mathlib's
([Algebra/Group/Action/Defs.lean, line 148, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Group/Action/Defs.lean#L148)).

**Inertia and decomposition.** Mathlib supplies the two subgroups

```lean
abbrev decompositionSubgroup (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  MulAction.stabilizer (L ≃ₐ[K] L) A

noncomputable def inertiaSubgroup (A : ValuationSubring L) : Subgroup (A.decompositionSubgroup K) :=
  MonoidHom.ker <|
    MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)
```

([RingTheory/Valuation/RamificationGroup.lean, lines 30 and 50, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Valuation/RamificationGroup.lean#L30-L50)),
which is §4 verbatim: the stabilizer of the valuation ring, and the kernel of
the action on its residue field. Because the inertia subgroup is a subgroup of
the decomposition group while FLT wants it inside the full group, it pushes it
forward and then states unramifiedness

```lean
def inertiaSubgroupIn (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype
```
```lean
def GaloisRepUnramifiedAt (W' : Affine R) (n : ℕ) (q : ℕ) : Prop :=
  ∀ A : ValuationSubring K, A.LiesOverPrime q →
    ∀ σ ∈ A.inertiaSubgroupIn S,
    ∀ x : Submodule.torsionBy ℤ (W'⁄K).Point n, σ • x = x
```

([Def_FLTPrelim_Ramification.lean, lines 21–38](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Ramification.lean#L21-L38)),
with `LiesOverPrime A q` meaning `(q : L) ∈ A.nonunits`
([line 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Ramification.lean#L16)).

**The correspondences.** The finite layer has the two operations
`IntermediateField.fixedField` and `IntermediateField.fixingSubgroup` with the
adjunction and definiteness ([FieldTheory/Galois/Basic.lean, lines 210, 229, 232
and 273, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean#L210-L273));
the infinite layer replaces subgroups by closed ones
([FieldTheory/Galois/Infinite.lean, line 196](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Infinite.lean#L196))
and the group is profinite
([FieldTheory/Galois/Profinite.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Profinite.lean)).
FLT uses the finite layer to name invariants (`F.fixingSubgroup` for an
intermediate field $`F`$, [Def_GaloisRep_OrdinaryUnitClasses.lean, line 39](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_OrdinaryUnitClasses.lean#L39)) and
to descend scalars (`AlgEquiv.ofRingEquiv`, [Def_PadicAlgCl_RingOfIntegers.lean,
line 116](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_PadicAlgCl_RingOfIntegers.lean#L116)).

### Key point → declaration map

| Mathematics | Lean declaration | Location |
|---|---|---|
| an extension: an embedding $`S \hookrightarrow K`$ | `Algebra S K` | [Def_FLTPrelim_GaloisRep.lean 21–23](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean#L21-L23) |
| a tower, and the commuting triangle | `IsScalarTower R S K` | [Action/Defs.lean 210](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Group/Action/Defs.lean#L210) |
| $`\bar{\mathbb{Q}}`$ as algebraic + algebraically closed | `AlgebraicClosure ℚ`, `IsAlgClosure` | [IsAlgClosed/Basic.lean 264, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/IsAlgClosed/Basic.lean#L264) |
| algebraic, algebraically closed | `Algebra.IsAlgebraic`, `IsAlgClosed` | [Algebraic/Defs.lean 68](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Algebraic/Defs.lean#L68), [IsAlgClosed/Basic.lean 62](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/IsAlgClosed/Basic.lean#L62) |
| normal, separable | `Normal`, `Algebra.IsSeparable` | [Normal/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Normal/Basic.lean), [Separable.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Separable.lean) |
| an algebraic closure is normal and (in char 0) separable | `IsAlgClosure.normal`, `IsAlgClosure.separable` | [IsAlgClosed/Basic.lean 275–282](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/IsAlgClosed/Basic.lean#L275-L282) |
| the Galois group, as a type | `AlgEquiv`, notation `≃ₐ[S]` | [Algebra/Equiv.lean 31–42](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Algebra/Equiv.lean#L31-L42) |
| normal + separable | `IsGalois` | [Galois/Basic.lean 54–59](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean#L54-L59) |
| $`\bar{\mathbb{Q}}/\mathbb{Q}`$ is Galois | `AlgebraicClosure.Rat.isGalois` | [Def_FieldTheory_RatAlgClosureGalois.lean 5–7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FieldTheory_RatAlgClosureGalois.lean#L5-L7) |
| the action of a field automorphism on points | `Point.map`, then `SMul`/`DistribMulAction` | [Affine/Point.lean 793–799](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean#L793-L799), [Def_FLTPrelim_GaloisRep.lean 25–41](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean#L25-L41) |
| the $`\mathbb{Z}/n`$-module on $`n`$-torsion | `instModuleZModTorsionBy` | [Def_FLTPrelim_GaloisRep.lean 60–65](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean#L60-L65) |
| two commuting actions | `SMulCommClass` | [Action/Defs.lean 148](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Group/Action/Defs.lean#L148) |
| the representation as a monoid hom | `galoisRep`, `DistribMulAction.toModuleAut` | [Def_FLTPrelim_GaloisRep.lean 25–41](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean#L25-L41), [Module/Equiv/Basic.lean 201](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/Equiv/Basic.lean#L201) |
| a Galois-stable submodule | `IsGaloisStable` | [Def_FLTPrelim_GaloisRep.lean 68–70](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean#L68-L70) |
| irreducible: no stable line | `GaloisRepIsIrreducible` | [Def_FLTPrelim_GaloisRep.lean 74–77](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean#L72-L77) |
| a cofixed line | `HasGaloisStableCofixedLine` | [Def_FLTPrelim_CofixedLine.lean 15–19](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_CofixedLine.lean#L15-L19) |
| decomposition and inertia subgroups | `decompositionSubgroup`, `inertiaSubgroup` | [RamificationGroup.lean 30, 50](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Valuation/RamificationGroup.lean#L30-L50) |
| unramified at $`q`$ | `inertiaSubgroupIn`, `GaloisRepUnramifiedAt` | [Def_FLTPrelim_Ramification.lean 21–38](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Ramification.lean#L21-L38) |
| fixed field, fixing subgroup | `IntermediateField.fixedField`, `IntermediateField.fixingSubgroup` | [Galois/Basic.lean 210, 229](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean#L210-L229) |
| the infinite correspondence (closed subgroups) | `IntermediateFieldEquivClosedSubgroup` | [Galois/Infinite.lean 196](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Infinite.lean#L196) |
| a Galois character: the determinant | `LinearEquiv.det` | [Def_FreyPackage_DetCyclotomic.lean 20–21](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FreyPackage_DetCyclotomic.lean#L20-L26) |
| the cyclotomic character | `modularCyclotomicCharacter` | [CyclotomicCharacter.lean 212](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean#L212) |
| complex conjugation, via a real place | `AlgEquiv.restrictNormalHom` | [Def_GaloisRep_ComplexConjugation.lean 14–31](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_ComplexConjugation.lean#L14-L31) |

## 8. Small traps (reading the code)

- **`≃ₐ[S]` and `≃+*` are different types.** FLT passes Galois elements where
  ring automorphisms are wanted by explicit ascription,
  `(σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)`
  ([Def_ExtCitation_AdmissibleExtension.lean, line 27](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ExtCitation_AdmissibleExtension.lean#L27)),
  because mathlib's `modularCyclotomicCharacter` is a monoid hom on `L ≃+* L`.
  The coercion `AlgEquiv → RingEquiv` exists; the reverse direction only through
  explicit constructions (`AlgEquiv.ofRingEquiv`, or the `ℕ`/`ℤ`-base
  `toNatAlgEquiv`/`toIntAlgEquiv`).
- **Do not read `S` as "an intermediate field".** In `K ≃ₐ[S] K`, `S` is the
  base of the action of §3. When `W'` is a curve over `R`, the curve is
  base-changed to `K` over `R` while the automorphisms are over `S`; the
  `IsScalarTower` binder is what reconciles the two.
- **Characteristic zero is doing work in two places**, not one: it makes
  algebraic extensions separable (§2), and it makes an algebraically closed field
  contain `n` distinct `n`-th roots of unity for every `n` — the hypothesis
  `hn : Nat.card (rootsOfUnity n K) = n` under which the mod-`n` cyclotomic
  character takes values in `(ZMod n)ˣ` rather than in a residue ring attached
  to a possibly smaller root group.
- **`attribute [-instance] AlgebraicClosure.Rat.isGalois`** (and the similar
  disabling of `instDecEqAlgebraicClosureRat` and of the torsion action
  instances) is performance engineering, not mathematics. A file that *uses*
  the Galois structure re-enables it locally, so a Galois-theoretic step that
  does not look available usually means a locally re-enabled instance rather
  than a missing lemma.
- **`Gal(K/F)` is notation, not a definition.** Its expansion is `K ≃ₐ[F] K`; if
  a grep for `Gal` finds nothing, look for `≃ₐ[`.

## 9. Links

File-level pointers; the anchored citations are inline above.

FLT sources at the pinned sha `aa2d8b3`:

- [Def_FLTPrelim_GaloisRep.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean) — the `R`/`S`/`K` tower, the action on torsion, `IsGaloisStable`, `GaloisRepIsIrreducible`
- [Def_FLTPrelim_CofixedLine.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_CofixedLine.lean) — `HasGaloisStableCofixedLine`
- [Def_FreyPackage_GaloisRep.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FreyPackage_GaloisRep.lean) — `galoisRep`, `freyGaloisRep`
- [Def_FreyPackage_DetCyclotomic.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FreyPackage_DetCyclotomic.lean) — `galoisRepDet`, `GaloisRepDetEqCyclotomic`
- [Def_FLTPrelim_Ramification.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Ramification.lean) — `LiesOverPrime`, `inertiaSubgroupIn`, `GaloisRepUnramifiedAt`
- [Def_FieldTheory_RatAlgClosureGalois.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FieldTheory_RatAlgClosureGalois.lean) — the `IsGalois ℚ ℚ̄` instance
- [Def_GaloisRep_ComplexConjugation.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_ComplexConjugation.lean) — complex conjugation in the absolute group
- [Def_ExtCitation_AdmissibleExtension.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ExtCitation_AdmissibleExtension.lean) — roots-of-unity counting, `modularCyclotomicCharacter` in use
- [Def_GaloisRep_OrdinaryUnitClasses.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_OrdinaryUnitClasses.lean) and [Def_PadicAlgCl_RingOfIntegers.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_PadicAlgCl_RingOfIntegers.lean) — intermediate-field uses of `fixingSubgroup`
- [Def_FLTPrelim_FreyPackage.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_FreyPackage.lean) — `freyCurveInt` over `ℤ` and `freyCurve` over `ℚ`

Mathlib at tag `v4.33.0`:

- [`AlgEquiv` and the `≃ₐ` notation](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Algebra/Equiv.lean) — [lines 31–42](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Algebra/Equiv.lean#L31-L42)
- [`SMulCommClass` and actions](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Group/Action/Defs.lean) — [line 148](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Group/Action/Defs.lean#L148)
- [`Algebra.IsAlgebraic`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Algebraic/Defs.lean) — [line 68](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Algebraic/Defs.lean#L68)
- [`IsAlgClosed`, `IsAlgClosure`, normal/separable instances](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/IsAlgClosed/Basic.lean) — [62](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/IsAlgClosed/Basic.lean#L62), [264](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/IsAlgClosed/Basic.lean#L264), [275](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/IsAlgClosed/Basic.lean#L275)
- [`IsGalois`, fixed field, fixing subgroup](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean) — [54–59](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean#L54-L59), [210](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean#L210), [229](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean#L229), [590](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean#L590)
- [The `Gal(L/K)` notation](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Notation.lean) — [line 35](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Notation.lean#L35)
- [Infinite Galois theory](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Infinite.lean) — [line 196](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Infinite.lean#L196)
- [Profinite Galois groups](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Profinite.lean)
- [`AlgEquiv.restrictNormalHom`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Normal/Defs.lean) — [line 195](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Normal/Defs.lean#L195)
- [`DistribMulAction.toModuleAut`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/Equiv/Basic.lean) — [line 201](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/Equiv/Basic.lean#L201)
- [`Point.map`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean#L799) and [the `⁄` base-change notation](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean#L268)
- [Decomposition and inertia subgroups](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Valuation/RamificationGroup.lean#L30-L50)
- [`modularCyclotomicCharacter`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean#L212)

Companion notes:

- [007 — The Weil pairing](007-weil-pairing.md) — the determinant and the cyclotomic character from the pairing
- [010 — Finite fields, Frobenius, and point counts](010-finite-fields-frobenius-and-point-counts.md) — where the characteristic polynomial of a Frobenius is taken
- [math/003](../math/003-galois-rep-irreducible-in-english.md), [math/004](../math/004-irreducible-and-cofixed-line.md), [math/006](../math/006-fixed-or-cofixed-and-inertia.md) — the predicates and the dichotomy of §5 in use
