# Field extensions and Galois theory at the mathlib level

First of the `base/` notes, which document the foundational mathlib layers the
FLT proof rests on: the layers that are *not* part of FLT's own argument but
which every statement in `Definitions/` is written against.

Companion notes in [`../math/`](../math/): 003 and 004 (the predicates
`GaloisRepIsIrreducible` and `HasGaloisStableCofixedLine`), 005 (why the
$`p`$-torsion of the Frey curve is $`\mathbb{F}_p^2`$), 006 (fixed or cofixed,
where inertia decides). This note supplies what those four take for granted:
the field-theoretic and Galois-theoretic vocabulary. The running example is
the one object all of them share, `AlgebraicClosure ℚ`, together with its
automorphism group as mathlib and FLT actually spell them.

Line numbers refer to `anthropics/fermats-last-theorem@aa2d8b3`
(main, 2026-09-03); mathlib line numbers refer to tag **v4.33.0**
(`db584cd6…`, the rev pinned in `lake-manifest.json`).

## 1. Why field theory is the substrate

Everything in the proof happens inside one field: the algebraic closure
$`\overline{\mathbb{Q}}`$ of $`\mathbb{Q}`$. The elementary statement "there is
a degree-$`p`$ rational isogeny" becomes "the absolute Galois group
$`\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})`$ admits a stable line in
$`E_P[p]`$", and that group is not an ad-hoc object: it is the group of field
automorphisms of $`\overline{\mathbb{Q}}`$ fixing $`\mathbb{Q}`$.

Two consequences shape the whole formalization:

- **Facts about $`\overline{\mathbb{Q}}`$ must come from the algebraic-closure
  interface**, not from an intuition about a fixed "big field". Mathlib does
  not have one canonical algebraic closure; `AlgebraicClosure k` is *a* type
  with the property `IsAlgClosure k (AlgebraicClosure k)`, and `IsAlgClosure`
  is the bundle of exactly two properties (algebraic + algebraically closed).
  Every classical fact the proof uses — a curve with coefficients in $`\mathbb{Q}`$
  has all of its $`n`$-torsion defined over $`\overline{\mathbb{Q}}`$; there are
  exactly $`n`$ $`n`$-th roots of unity there — is a theorem about *any* such
  type.
- **The Galois group is encoded as a type, not as a named group.** There is no
  `GaloisGroup` structure; the group is the type `K ≃ₐ[S] K` of $`S`$-algebra
  automorphisms of `K`, built from bijective `S`-algebra homomorphisms with
  group structure from composition.

## 2. Layer 1: what an extension *is* — `Algebra`, not a "field tower"

The most visible difference from textbook vocabulary: mathlib never says
"$`K/S`$ is a field extension". The data is an **algebra structure**, i.e. a
ring homomorphism $`S \to K`$:

```lean
-- Def_FLTPrelim_GaloisRep.lean, lines 21–23
variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]
```

Reading this from left to right:

| Binder | Meaning | In our example |
|---|---|---|
| `[CommRing R]`, `[CommRing S]`, `[Field K]` | the curve is defined over a *ring* `R` | `R = ℚ` |
| `[Algebra R S]`, `[Algebra R K]` | `S` and `K` are `R`-algebras | `ℚ → ℚ`, `ℚ → ℚ̄` |
| `[Algebra S K]` | `K` is an `S`-algebra — "`K` extends `S`" | `ℚ → ℚ̄` again |
| `[IsScalarTower R S K]` | the two `R`-structures on `K` agree through `S` | automatic here |

`IsScalarTower R S K` is no subtlety: for `CommRing`s it is the equation
`algebraMap S K (algebraMap R S r) = algebraMap R K r`, i.e. the triangle
commutes. It is what makes `K ≃ₐ[S] K` a quotient-like "over `S`" notion while
`W'` still lives over `R`: the base change `W'⁄K` is taken over `R`, and `K` is
simultaneously an `S`-algebra, so an `S`-automorphism acts on it.

### Why the generality, and what it does *not* mean

The predicate `GaloisRepIsIrreducible` is stated for `W' : Affine R` over an
arbitrary commutative ring, with `S` a further commutative ring mapping to
`K`. **Every concrete instantiation in this repository pins `R = S = ℚ` and
`K = AlgebraicClosure ℚ`** — a survey of the named-argument uses of
`galoisRep`, `galoisRepModuleEnd` and `inertiaSubgroupIn` finds only `S := ℚ`,
never `S := ℚ_[p]` or a number field. So the generality is a property of *where
the definitions live*, not a feature any step of the FLT argument exercises:

1. **`R` a ring, not a field** — these definitions sit in the general
   Weierstrass-curve namespace and are inherited from the ICL port, whose
   `R` was the coefficient ring rather than the field of definition. It costs
   nothing: `[CommRing R]` is what the base-change and group-law theory is
   stated under anyway. (FLT does separately use `P.freyCurveInt :
   WeierstrassCurve ℤ` ([Def_FLTPrelim_FreyPackage.lean, lines 83–89](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_FreyPackage.lean)),
   but for the reduction and semistability arguments, not through this
   predicate.)
2. **`S` the base of the action** — the reason `S` is a parameter and not
   hard-wired to `R` is that the Galois action is naturally *over the field of
   definition*, and it is the `Point.map` binder (`F →ₐ[S] K`, §5) that
   requires it. At the concrete level, the local-at-$`p`$ automorphisms are
   indeed over `ℚ_[p]`, but FLT builds them as their own type
   (`localAut : primeLocalGaloisGroup (pPrime p) → PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p`,
   [Def_GaloisRep_LocalFlatClasses.lean, line 14](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_GaloisRep_LocalFlatClasses.lean))
   rather than by instantiating this tower.
3. **`S = R`** — the case of the Frey curve. The exotic-looking binders then
   collapse to `[Algebra ℚ ℚ]` and the identity `[IsScalarTower ℚ ℚ ℚ̄]`.

This is the "general `Affine R`" puzzle of [note 003](../math/003-galois-rep-irreducible-in-english.md)
one level up: there the question was why `P.freyCurve : WeierstrassCurve ℚ`
fits a `W' : Affine R` binder; here it is why a statement about
`ℚ ≃ₐ[ℚ] ℚ̄` fits a `K ≃ₐ[S] K` binder. Both are answered by unification plus
instance search — and in both cases it pays to know that the general form is
inherited rather than needed.

### The base change notation

`W'⁄K` is `WeierstrassCurve.Affine.baseChange W' K`, a **scoped notation**
mathlib defines ([Affine/Basic.lean, line 268, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean)):

```lean
scoped notation:max W:max "⁄" S:max => baseChange W S
```

FLT files therefore carry `open scoped WeierstrassCurve.Affine` to see it (e.g.
[Def_FreyPackage_GaloisRep.lean, line 33](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FreyPackage_GaloisRep.lean)).
For coefficients already in `ℚ`, `P.freyCurve⁄(AlgebraicClosure ℚ)` is the same
equation read over $`\overline{\mathbb{Q}}`$ — which is why the notation is
needed at all: `Point.map` acts on the base-changed curve, not on the curve
over `ℚ`, and the two only agree through `Algebra`.

## 3. Layer 2: algebraic, separable, normal — the adjectives

These are `Prop`-valued classes on an algebra `R → K`; each is an assertion
about elements (or minimal polynomials), and mathlib can infer them for
algebraic closures.

| Lean | Math | Where |
|---|---|---|
| `Algebra.IsAlgebraic R K` | every $`x \in K`$ is a root of a nonzero polynomial over `R` | [RingTheory/Algebraic/Defs.lean, line 68, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Algebraic/Defs.lean) |
| `IsAlgClosed K` | every nonconstant polynomial over `K` has a root | [FieldTheory/IsAlgClosed/Basic.lean, line 62, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/IsAlgClosed/Basic.lean) |
| `IsAlgClosure R K` | `IsAlgClosed K` **and** `Algebra.IsAlgebraic R K` (with `IsTorsionFree R K` an instance argument) | same file, line 264, v4.33.0 |
| `Normal R K` | minpolys over `R` split in `K` | [FieldTheory/Normal/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Normal/Basic.lean) |
| `Algebra.IsSeparable R K` | minpolys have distinct roots (a field-level notion) | [FieldTheory/Separable.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Separable.lean) |

`IsAlgClosure` is the only one carrying an `Algebra R K` argument among the
"closure" notions, and mathlib's instances do the work:

```lean
-- Mathlib/FieldTheory/IsAlgClosed/Basic.lean, lines 275–282, v4.33.0
instance (priority := 100) IsAlgClosure.normal (R K : Type*) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] : Normal R K where
  toIsAlgebraic := IsAlgClosure.isAlgebraic
  splits' _ := (IsAlgClosure.isAlgClosed R).splits _

instance (priority := 100) IsAlgClosure.separable (R K : Type*) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] [CharZero R] : Algebra.IsSeparable R K :=
  ⟨fun _ => (minpoly.irreducible (Algebra.IsIntegral.isIntegral _)).separable⟩
```

The `[CharZero R]` in the second instance is the whole role of characteristic
zero in the setup: over a field of characteristic zero every algebraic
extension is separable. For $`R = \mathbb{Q}`$ both instances apply, and
together they give that $`\overline{\mathbb{Q}}/\mathbb{Q}`$ is Galois — see the
next section.

## 4. Layer 3: the Galois group, and `IsGalois`

The type is an **algebra equivalence**
([Algebra/Algebra/Equiv.lean, line 31, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Algebra/Equiv.lean)), with notation at line 42:

```lean
structure AlgEquiv (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
...
notation:50 A " ≃ₐ[" R "] " A' => AlgEquiv R A A'
```

An element of `A ≃ₐ[R] A` is a bijective `R`-algebra homomorphism; group
structure comes from composition. mathlib also has a scoped notation for the
Galois group of a *named* extension ([FieldTheory/Galois/Notation.lean, line 35, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Notation.lean)):

```lean
macro "Gal(" L:term:100 "/" K:term ")" : term => `($L ≃ₐ[$K] $L)
```

FLT almost never uses it and writes the type out in full. The consequence for a
reader: the absolute Galois group of $`\mathbb{Q}`$ appears in the sources as

```lean
AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ
```

e.g. [Def_GaloisRep_ComplexConjugation.lean, line 30](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_GaloisRep_ComplexConjugation.lean),
[Def_FreyPackage_GaloisRep.lean, lines 38–42](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FreyPackage_GaloisRep.lean).
mathlib happens to name this same object `Field.absoluteGaloisGroup`
([FieldTheory/AbsoluteGaloisGroup.lean, line 43, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/AbsoluteGaloisGroup.lean)), but only for its topological
abelianization; FLT does not use it.

**`IsGalois`** is exactly two of the adjectives above
([FieldTheory/Galois/Basic.lean, lines 54–59, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean)):

```lean
class IsGalois : Prop where
  [to_isSeparable : Algebra.IsSeparable F E]
  [to_normal : Normal F E]
```

Mathlib's general theorem that an algebraic closure is Galois needs a
characteristic-zero hypothesis ([FieldTheory/Galois/Basic.lean, lines 590–591, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean)):

```lean
instance (priority := 100) IsAlgClosure.isGalois (k K : Type*) [Field k] [Field K] [Algebra k K]
    [IsAlgClosure k K] [CharZero k] : IsGalois k K where
```

FLT spells the resulting instance out once, as a named global instance
([Def_FieldTheory_RatAlgClosureGalois.lean, lines 5–7](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FieldTheory_RatAlgClosureGalois.lean)):

```lean
instance AlgebraicClosure.Rat.isGalois :
    @IsGalois ℚ _ (AlgebraicClosure ℚ) _ DivisionRing.toRatAlgebra :=
  @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _
```

The two `@`-prefixed applications and the explicit `DivisionRing.toRatAlgebra`
are there because the instance must be stated with all typeclass arguments
pinned, not left to synthesis.

**Gotcha worth knowing before reading any FLT file.** This instance is
expensive for typeclass search, and FLT disables it file by file with
`attribute [-instance] AlgebraicClosure.Rat.isGalois`, usually inside a long
list of other disabled instances (e.g.
[Thm_MonoidHom_isOpen_ker_of_cycloCharSpec.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_MonoidHom_isOpen_ker_of_cycloCharSpec.lean),
which is where it is enabled). A reader who greps a `P2M/Sol/` file and finds
a Galois-theoretic step that is not "obviously" available should suspect a
locally re-enabled instance rather than a missing lemma.

## 5. What the action actually is: `Point.map`

The Galois group acts on torsion points through base change, and the chain is
short enough to quote. `Point.map` is a homomorphism of *groups*
([AlgebraicGeometry/EllipticCurve/Affine/Point.lean, lines 797–799, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean)):

```lean
variable [Algebra R S] ... [Algebra R K] [Algebra S K] [IsScalarTower R S K] ... (f : F →ₐ[S] K)
noncomputable def map : (W'⁄F).Point →+ (W'⁄K).Point where
```

note the binder: `map` is *defined for an `S`-algebra homomorphism* `F →ₐ[S] K`,
which is precisely why the `R → S → K` tower of §2 is in scope before any
Galois action can be spoken of. FLT then packages the action
([Def_FLTPrelim_GaloisRep.lean, lines 25–41](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean)):

```lean
noncomputable instance instSMulAlgEquiv : SMul (K ≃ₐ[S] K) (W'⁄K).Point :=
  ⟨fun σ P => Point.map σ.toAlgHom P⟩
```

and the module-automorphism repackaging of [note 004 §4](../math/004-irreducible-and-cofixed-line.md)
is mathlib's [Algebra/Module/Equiv/Basic.lean, line 201, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/Equiv/Basic.lean) `toModuleAut`:

```lean
noncomputable def galoisRep (W' : Affine R) (n : ℕ) :
    (K ≃ₐ[S] K) →*
      (Submodule.torsionBy ℤ (W'⁄K).Point n) ≃ₗ[ZMod n] (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  DistribMulAction.toModuleAut (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)
```

So "the Galois action" is three ordinary mathlib constructions: an `SMul` from
`Point.map`, a `DistribMulAction` (functoriality of `Point.map`), and a
`Module` structure on `n`-torsion — no representation theory enters until the
`→*` of `galoisRep` is formed.

## 6. Inertia and decomposition: the only local input

The one genuinely Galois-theoretic notion FLT invents a name for is unramified
at a prime; mathlib supplies the two subgroups
([RingTheory/Valuation/RamificationGroup.lean, lines 30 and 50, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Valuation/RamificationGroup.lean)):

```lean
abbrev decompositionSubgroup (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  MulAction.stabilizer (L ≃ₐ[K] L) A

noncomputable def inertiaSubgroup (A : ValuationSubring L) : Subgroup (A.decompositionSubgroup K) :=
  MonoidHom.ker <|
    MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)
```

In words: `A : ValuationSubring L` is a valuation ring of the big field `L`
(the formal stand-in for a place); the **decomposition subgroup** is the
stabilizer of `A` under the action of `L ≃ₐ[K] L`; the **inertia subgroup** is
the kernel of the induced action on the residue field, i.e. those automorphisms
that preserve `A` and act trivially on `A` modulo its maximal ideal. Note that
the decomposition group lands directly in `L ≃ₐ[K] L`, whereas `inertiaSubgroup`
is a subgroup of the decomposition group — which is why FLT has to push it
forward
([Def_FLTPrelim_Ramification.lean, lines 21–22](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_Ramification.lean)):

```lean
def inertiaSubgroupIn (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype
```

and then says "unramified at `q`" as "every inertia element of every valuation
ring `q` lies over acts trivially on the `n`-torsion"
([Def_FLTPrelim_Ramification.lean, lines 35–38](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_Ramification.lean)):

```lean
def GaloisRepUnramifiedAt (W' : Affine R) (n : ℕ) (q : ℕ) : Prop :=
  ∀ A : ValuationSubring K, A.LiesOverPrime q →
    ∀ σ ∈ A.inertiaSubgroupIn S,
    ∀ x : Submodule.torsionBy ℤ (W'⁄K).Point n, σ • x = x
```

with `LiesOverPrime A q` meaning `(q : L) ∈ A.nonunits` (line 16). This is the
predicate whose role [note 006](../math/006-fixed-or-cofixed-and-inertia.md)
explains; the point here is that its ingredients — stabilizers, kernels,
residue fields, the `S`-algebra structure on `K` — are all mathlib-level field
theory. `S` stays a parameter for the reason of §2: the construction is
"automorphisms of `K` over its field of definition", and only `S = ℚ` is ever
instantiated here, even for the local questions at a prime $`q`$, where the
relevant local group is the inflation of the decomposition group of a valuation
ring rather than a group over $`\mathbb{Q}_q`$.

## 7. The two Galois-correspondence layers mathlib offers

Neither is used in the irreducibility step, but both are used elsewhere in the
project, and knowing which is which prevents a lot of confusion.

**Finite layer.** For a finite extension, mathlib proves the fundamental
theorem and the useful special cases. The two operations are
`IntermediateField.fixedField` (a subgroup ↦ its fixed field,
[FieldTheory/Galois/Basic.lean, line 210, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean)) and
`IntermediateField.fixingSubgroup` (an intermediate field ↦ the subgroup fixing
it, line 229), with the adjunction `K ≤ fixedField H ↔ H ≤ fixingSubgroup K`
(line 232) and definiteness `fixingSubgroup (fixedField H) = H` (line 273).
Typical uses in FLT are to define "an element fixed by a subgroup", e.g.
`F.fixingSubgroup` with `F : IntermediateField ℚ ℚ̄` in
[Def_GaloisRep_OrdinaryUnitClasses.lean, lines 37–39](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_GaloisRep_OrdinaryUnitClasses.lean),
or to descend scalars: `AlgEquiv.ofRingEquiv` produces
`ℚ̄_p ≃ₐ[ringOfIntegers p K] ℚ̄_p` from an element of `K.fixingSubgroup`
([Def_PadicAlgCl_RingOfIntegers.lean, lines 110–128](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_PadicAlgCl_RingOfIntegers.lean)).

**Infinite layer.** For $`K/S`$ algebraic but not finite — the actual case,
$`\overline{\mathbb{Q}}/\mathbb{Q}`$ — the correspondence must be with *closed*
subgroups for the Krull topology: `IntermediateFieldEquivClosedSubgroup`
([FieldTheory/Galois/Infinite.lean, line 196, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Infinite.lean)), together with
`fixingSubgroup_isClosed` (line 64) and `normal_iff_isGalois` (line 261).
Equivalently `Gal(K/S)` is a profinite group
([FieldTheory/Galois/Profinite.lean, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Profinite.lean)).
The moral for the FLT side: "the representation is continuous" is *not*
formalized as a topological condition on a map out of the absolute Galois
group; where the project needs finiteness it produces an explicit finite
intermediate field, as in the `∃ F : IntermediateField ℚ ℚ̄, FiniteDimensional ℚ F ∧ …`
clause above.

## 8. Where the layer is cashed in

| Use | Mathematical content | Where |
|---|---|---|
| the ambient field | $`\overline{\mathbb{Q}}`$ as *a* type with `IsAlgClosure ℚ`, not a chosen field | `AlgebraicClosure ℚ`, `IsAlgClosure` ([FieldTheory/IsAlgClosed/Basic.lean:264](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/IsAlgClosed/Basic.lean)) |
| $`\overline{\mathbb{Q}}/\mathbb{Q}`$ is Galois | normal (all minpolys split) + separable (characteristic 0) | [Def_FieldTheory_RatAlgClosureGalois.lean:5–7](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FieldTheory_RatAlgClosureGalois.lean) |
| the group is `K ≃ₐ[S] K` | $`S`$-algebra automorphisms, with `S` the *field of definition* of the action | [Def_FLTPrelim_GaloisRep.lean:21–23](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean) |
| the action on points | `Point.map` for an `S`-algebra map, then `SMul`/`DistribMulAction` | [Def_FLTPrelim_GaloisRep.lean:25–41](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean) |
| the group as a monoid hom | `DistribMulAction.toModuleAut` | [Def_FreyPackage_GaloisRep.lean:18–21](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FreyPackage_GaloisRep.lean) |
| a Galois character | `LinearEquiv.det` of that automorphism | [Def_FreyPackage_DetCyclotomic.lean:20–26](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FreyPackage_DetCyclotomic.lean) |
| cyclotomic character | needs the count of roots of unity, hence `IsAlgClosed` at characteristic 0 | `IsAlgClosed.card_rootsOfUnity_eq` ([Def_ExtCitation_AdmissibleExtension.lean:7–10](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_ExtCitation_AdmissibleExtension.lean)); `modularCyclotomicCharacter` ([CyclotomicCharacter.lean:212, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean)) |
| complex conjugation as an element of the group | a real place, cut out via `AlgEquiv.restrictNormalHom` from an automorphism of $`\mathbb{C}`$ | [Def_GaloisRep_ComplexConjugation.lean:14–31](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_GaloisRep_ComplexConjugation.lean) |
| ramification | `ValuationSubring.decompositionSubgroup`, `.inertiaSubgroup`; two extension levels bridged by `.inertiaSubgroupIn` | [RamificationGroup.lean:30,50, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Valuation/RamificationGroup.lean); [Def_FLTPrelim_Ramification.lean:16–38](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_Ramification.lean) |

## 9. Small traps

- **`≃ₐ[S]` versus `≃+*`.** They are different types. FLT passes Galois
  elements where ring automorphisms are wanted by explicit ascription:
  `(σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)` in
  [Def_ExtCitation_AdmissibleExtension.lean, line 27](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_ExtCitation_AdmissibleExtension.lean),
  because mathlib's `modularCyclotomicCharacter` is a monoid hom on `L ≃+* L`.
  The coercion `AlgEquiv → RingEquiv` exists; the reverse direction exists only
  through explicit constructions (`AlgEquiv.ofRingEquiv`, or the `ℕ`/`ℤ`-base
  `toNatAlgEquiv`/`toIntAlgEquiv`), never as a coercion.
- **Do not read `S` as "an intermediate field".** In
  `K ≃ₐ[S] K`, `S` is the base of the action. When `W'` is a curve over `R`,
  the curve is base-changed to `K` over `R`, while the automorphisms are over
  `S`; that is exactly what the `IsScalarTower` binder reconciles.
- **Characteristic zero is doing work in two places**, not one: it makes
  algebraic extensions separable (§3), and it makes an algebraically closed
  field contain `n` distinct `n`-th roots of unity for every `n`, which is the
  hypothesis `hn : Nat.card (rootsOfUnity n K) = n` under which the mod-`n`
  cyclotomic character takes values in `(ZMod n)ˣ` rather than in a residue
  ring attached to a possibly smaller root group (§8).
- **`attribute [-instance] AlgebraicClosure.Rat.isGalois`** (and the similar
  disabling of `instDecEqAlgebraicClosureRat` and of the torsion action
  instances) is performance engineering, not a mathematical statement. Files
  that *use* the Galois structure re-enable it locally.
- **`Gal(K/F)` is notation, not a definition.** Its expansion is
  `K ≃ₐ[F] K`; if a grep for `Gal` finds nothing, look for `≃ₐ[` instead.

## 10. Links

FLT sources at the pinned sha `aa2d8b3` (raw):

- [Def_FLTPrelim_GaloisRep.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean) — the `R`/`S`/`K` tower, `SMul`/`DistribMulAction`, the two predicates
- [Def_FreyPackage_GaloisRep.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FreyPackage_GaloisRep.lean) — `galoisRep`, `freyGaloisRep`
- [Def_FreyPackage_DetCyclotomic.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FreyPackage_DetCyclotomic.lean) — `galoisRepDet`, `GaloisRepDetEqCyclotomic`
- [Def_FLTPrelim_Ramification.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_Ramification.lean) — `LiesOverPrime`, `inertiaSubgroupIn`, `GaloisRepUnramifiedAt`
- [Def_FieldTheory_RatAlgClosureGalois.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FieldTheory_RatAlgClosureGalois.lean) — the `IsGalois ℚ ℚ̄` instance
- [Def_GaloisRep_ComplexConjugation.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_GaloisRep_ComplexConjugation.lean) — complex conjugation in the absolute group
- [Def_ExtCitation_AdmissibleExtension.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_ExtCitation_AdmissibleExtension.lean) — roots-of-unity counting, `modularCyclotomicCharacter` in use
- [Def_GaloisRep_OrdinaryUnitClasses.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_GaloisRep_OrdinaryUnitClasses.lean) and [Def_PadicAlgCl_RingOfIntegers.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_PadicAlgCl_RingOfIntegers.lean) — intermediate-field uses of `fixingSubgroup`
- [Def_FLTPrelim_FreyPackage.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_FreyPackage.lean) — `freyCurveInt` over `ℤ` and `freyCurve` over `ℚ`

Mathlib v4.33.0 (line numbers as cited above):

- [`AlgEquiv` and the `≃ₐ` notation](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Algebra/Equiv.lean)
- [`IsScalarTower`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Group/Action/Defs.lean)
- [`Algebra.IsAlgebraic`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Algebraic/Defs.lean)
- [`IsAlgClosed`, `IsAlgClosure`, and the normal/separable instances](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/IsAlgClosed/Basic.lean)
- [`IsGalois`, fixed field, fixing subgroup, `IsAlgClosure.isGalois`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean)
- [The `Gal(L/K)` notation](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Notation.lean)
- [Infinite Galois theory (closed subgroups, Krull topology)](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Infinite.lean)
- [Profinite Galois groups](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Profinite.lean)
- [`AlgEquiv.restrictNormalHom`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Normal/Defs.lean)
- [`DistribMulAction.toModuleAut`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/Equiv/Basic.lean)
- [`Point.map` and the `⁄` base-change notation](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean)
- [Decomposition and inertia subgroups](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Valuation/RamificationGroup.lean)
- [`modularCyclotomicCharacter`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean)
- [`Field.absoluteGaloisGroup`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/AbsoluteGaloisGroup.lean)
