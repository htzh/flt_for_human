# Divisors and Pic⁰ for a function field

Eighth of the `base/` notes. [007](007-weil-pairing.md) covered torsion and the
Weil pairing; this note covers the other half of the curve vocabulary that the
FLT proof runs on — **places, divisors, linear equivalence, and the degree-zero
divisor class group the code calls `Pic0`**, which is how FLT writes down the
group of points of a Jacobian without ever constructing a variety. §4 ends with
the `pymath` demo that computes the genus-one case, where that Jacobian is the
curve itself.

The whole layer is the project's own. Mathlib has the ingredients — valuation
subrings, height-one spectra, residue fields, `finrank`, `Finsupp` — but no
`Place`/`Divisor`/`Pic` for a function field, no Serre duality, and no
Riemann–Roch. FLT supplies them in `Definitions/Def_AlgebraicCurve_*.lean`, and
[studies/hecke-commute-bar-survey.md §2](../studies/hecke-commute-bar-survey.md)
is the survey that motivated this note. What follows is the mathematics those
files encode, section by section, with the Lean quoted verbatim and organized
around the definitions rather than around the file list.

Line-number citations point at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib
citations point at tag **v4.33.0**. Both are rendered GitHub links.

## 1. Places: a closed point, encoded as a valuation subring

The classical object is a closed point of the curve, i.e. the local ring of a
point together with its maximal ideal. The code encodes it as the local ring
alone, and recovers the rest:

```lean
structure Place where
  toValuationSubring : ValuationSubring F
  algebraMap_mem' : ∀ a : K, algebraMap K F a ∈ toValuationSubring
  ne_top' : toValuationSubring ≠ ⊤
  isPrincipalIdealRing' : IsPrincipalIdealRing toValuationSubring
```

([Def_AlgebraicCurve_DivisorClassGroup.lean, lines 22–29](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L22-L29)).
The four fields are exactly the four things a closed point is:

- `toValuationSubring` is the local ring, a `ValuationSubring F`
  ([ValuationSubring.lean, line 41](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Valuation/ValuationSubring.lean#L41)),
  i.e. a subring whose elements or whose inverses are "integral" — the algebraic
  way of saying "the functions regular at the point";
- `algebraMap_mem'` says the constant field $`K`$ is regular everywhere, so the
  point is a $`K`$-point (of the curve, not of a base change);
- `ne_top'` says the local ring is not all of $`F`$: the point exists;
- `isPrincipalIdealRing'` is the crucial one for a smooth curve: the local ring
  is a principal ideal ring, hence a discrete valuation ring, which the code
  registers as an instance
  ([line 73](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L73)).

From those four fields the code builds the rest of the local data. The residue
field is the residue field of the local ring, and the **degree** of the point is
its dimension over $`K`$:

```lean
abbrev ResidueField : Type _ := IsLocalRing.ResidueField v.toValuationSubring

def deg : ℕ := Module.finrank K v.ResidueField
```

([lines 88–90](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L88-L90)),
with `Module.finrank` from
[Finrank.lean, line 62](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/LinearAlgebra/Dimension/Finrank.lean#L62).
The class `FiniteResidue` records when that dimension is finite
([lines 92–93](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L92-L93));
over $`\bar{\mathbb{Q}}`$ it always is, and §4 uses the fact that there it is
exactly $`1`$.

The order of vanishing at the point comes from the height-one spectrum of the
local ring, which is mathlib's notion of a closed point of the spectrum of a
Dedekind domain
([HeightOneSpectrum, Ideal/Lemmas.lean, line 493](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean#L493)),
hence a valuation:

```lean
def adicValuation : Valuation F ℤᵐ⁰ := v.heightOneSpectrum.valuation F
```

([line 102](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L102)).
That valuation takes values in $`\mathbb{Z}`$ up to units, so it carries a sign
ambiguity; the code resolves it once and for all by defining the **normalized
order**

```lean
def ord (f : F) : ℤ := -(WithZero.log (v.adicValuation f))
```

([line 122](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L122)),
with the sign chosen so that $`\mathrm{ord}_v(\pi) = +1`$ for a local
uniformizer. Its laws are the ones the divisor group will need: `ord_zero`,
`ord_one`, `ord_mul` (for nonzero arguments), `ord_inv`, and `ord_zpow`
([lines 125–149](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L125-L149)).
Two conventions are worth naming: $`\mathrm{ord}_v(0) = 0`$ rather than
$`+\infty`$ (the code never asks for the order of zero, and keeps the function
total), and the valuation is *normalized*, i.e. it is the height-one valuation
of the local ring, not some rational multiple of it.

## 2. Divisors: finitely supported integer functions

A divisor on a curve is a finite formal sum of points with integer
coefficients. In Lean that is a finitely supported function, so the definition
is one line:

```lean
abbrev Divisor : Type _ := Place K F →₀ ℤ
```

([line 179](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L179)).
The choice of `Finsupp` is not cosmetic — it *is* the free abelian group on the
set of places, with `Finsupp.support` supplying the finiteness that makes sums
over a divisor meaningful, and `Finsupp.single v n` the divisor $`n \cdot v`$.

Degree is the weighted sum of the coefficients, and the code packages it as an
additive homomorphism rather than a bare function:

```lean
def degree : Divisor K F →+ ℤ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulRight (v.deg : ℤ)
```

([lines 185–186](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L185-L186)).
`Finsupp.liftAddHom` builds the additive map from its values on the single-point
divisors, and each of those multiplies by the *degree of the point*; the
defining computation is the `@[simp]` lemma

```lean
theorem degree_single (v : Place K F) (n : ℤ) :
    degree (Finsupp.single v n) = n * v.deg
```

([lines 188–189](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L188-L189)).
Unfolded, the degree of a general divisor is the sum over its support
$`\sum_{v \in \mathrm{supp}\,D} D(v)\cdot\deg v`$ — a finite sum because that is
what `Finsupp` guarantees. Note the type: a single point has degree in
$`\mathbb{N}`$, a divisor in $`\mathbb{Z}`$, because the coefficients can be
negative.

The degree-zero divisors are the kernel of that map, one more one-liner:

```lean
def degZero : AddSubgroup (Divisor K F) := degree.ker
```

([line 193](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L193)),
with `mem_degZero` restating membership as $`\deg D = 0`$
([line 195](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L195)).

## 3. Principal divisors, and the residue theorem as a hypothesis

The divisor of a nonzero function is obtained by evaluating the normalized order
at every place:

```lean
def IsPrincipal (D : Divisor K F) : Prop := ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, D v = v.ord f

def principal : AddSubgroup (Divisor K F) where
  carrier := {D | IsPrincipal D}
  zero_mem' := ⟨1, one_ne_zero, fun v => by simp⟩
  add_mem' := by
    rintro D E ⟨f, hf, hD⟩ ⟨g, hg, hE⟩
    exact ⟨f * g, mul_ne_zero hf hg, fun v => by
      rw [Finsupp.add_apply, hD v, hE v, v.ord_mul hf hg]⟩
  neg_mem' := by
    rintro D ⟨f, hf, hD⟩
    exact ⟨f⁻¹, inv_ne_zero hf, fun v => by
      rw [Finsupp.neg_apply, hD v, v.ord_inv]⟩
```

([lines 198–210](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L198-L210)).
Read the three closure proofs as the three laws of a valuation: the divisor of
$`1`$ is zero (`ord_one`), the divisor of $`fg`$ is the sum (`ord_mul`), and the
divisor of $`f^{-1}`$ is the negative (`ord_inv`). That is the entire reason
`principal` is a subgroup, and it is the only place those laws are used.

Two points of substance are deliberately *not* proved here.

**Degree zero.** For a curve, a principal divisor has degree zero — the sum of
the orders of a function over all points vanishes, which is the residue theorem
(or "the degree of a principal divisor is zero"). The code turns that into a
class, so that it can be assumed exactly where it is known and not smuggled in:

```lean
class HasPrincipalDivisors : Prop where
  exists_divisor : ∀ f : F, f ≠ 0 → ∃ D : Divisor K F,
    (∀ v : Place K F, D v = v.ord f) ∧ Divisor.degree D = 0
```

([lines 217–219](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L217-L219)).
It is a hypothesis, not a theorem, because the whole `Place`/`Divisor` API is
stated for an arbitrary field extension $`F/K`$; there is no curve yet. The
class is *supplied* for the curves the proof cares about — for the modular
function field it is
`ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar`
([Thm file, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean#L10))
— and that instantiation is what makes §4 a statement about a Jacobian rather
than about a formal group.

**Finite fibres.** The same hypothesis is what makes the fibre of a place under
a finite extension finite (§5); again it is a theorem for the curve, not for a
general field extension.

With `principal` in hand, the two Picard groups are quotients:

```lean
abbrev Pic : Type _ := Divisor K F ⧸ Divisor.principal (K := K) (F := F)

abbrev Pic0 : Type _ :=
  Divisor.degZero (K := K) (F := F) ⧸
    (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))
```

([lines 221–225](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L221-L225)).
`Pic` is divisors modulo principal divisors: the class group of the curve, also
called the group of divisor classes under **linear equivalence**. `Pic0` is the
degree-zero part. The notation `⧸` is the quotient of an additive group by an
`AddSubgroup`, and the second definition is the one worth pausing over:
`addSubgroupOf` is mathlib's operation that restricts a subgroup to a subgroup
(the additive form of `Subgroup.subgroupOf`,
[Subgroup/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Group/Subgroup/Basic.lean)).
So `Pic0` is *not* the kernel of a homomorphism induced by `degree`; it is the
quotient of `degZero` by `principal ∩ degZero`. The two agree when principal
divisors have degree zero, but the code never needs that identification, and
phrasing it this way avoids having to prove that `degree` descends to `Pic`.

The quotient has the API one expects, all of it `rfl`-level or nearly so:
`Pic0.mk` is the class map, `mk_surjective` says every class is hit,
`mk_add`/`mk_zero` record that it is an additive homomorphism
([lines 231–240](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L231-L240)).
Torsion is by scalar:

```lean
def torsion (n : ℕ) : AddSubgroup (Pic0 K F)
```

([line 244](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L244)),
with `mem_torsion` saying $`x \in \mathrm{torsion}\;n \iff n \cdot x = 0`$
([line 247](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L247)).
That is the group whose size, for all $`n`$ at once, is the $`p`$-adic rank of
the Jacobian:

```lean
def AbelJacobiCard (p : ℕ) (g : ℕ) : Prop :=
  ∀ n : ℕ, Nat.card (Pic0.torsion K F (p ^ n)) = p ^ (2 * g * n)
```

([lines 252–253](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L252-L253)).
The name is the honest one: over $`\mathbb{C}`$ this count is what the
Abel–Jacobi map gives, a free $`\mathbb{Z}_p`$-module of rank $`2g`$; here it is
stated purely as a cardinality of divisor classes. This is the "rank $`2g`$"
that [007 §8](007-weil-pairing.md) quotes for the Tate module of $`J_0(N)`$.

## 4. The Jacobian, without a variety

The modular instance is two abbreviations:

```lean
abbrev modularFunctionFieldBar : IntermediateField (AlgebraicClosure ℚ)
    (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)

abbrev JZero : Type _ :=
  Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
```

([Def_ModularCurve_ArithmeticGalois.lean, lines 111–116](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ArithmeticGalois.lean#L111-L116)).
So `JZero N` is degree-zero divisor classes on $`\bar{\mathbb{Q}}(X_0(N))`$:
the $`\bar{\mathbb{Q}}`$-points of the Jacobian, realized as a quotient of
divisors. The code immediately records that the absolute Galois group acts on
it,

```lean
example : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero N) :=
  inferInstance
```

([line 118](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ArithmeticGalois.lean#L118)),
which is the divisor-level origin of every Galois representation the proof
attaches to $`J_0(N)`$.

Two facts make this the genuine group and not a formal shadow, and both are
theorems for this function field rather than hypotheses:

- `hasPrincipalDivisors_modularFunctionFieldBar` supplies
  `HasPrincipalDivisors` (conditional on the modular-polynomial family, i.e. on
  the input [006](006-the-modular-equation.md) and math/010 provide), so
  principal divisors are degree zero and the quotient is the honest class group
  ([Thm file, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean#L10));
- over $`\bar{\mathbb{Q}}`$ every place has degree one,
  `deg_eq_one_modularFunctionFieldBar`
  ([Thm file, line 12](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean#L12)),
  so the degree of a divisor is literally the number of points counted with
  multiplicity, and `degZero` is "as many zeros as poles".

What is *not* used here is worth saying explicitly, because three different
objects in this project are all called "the Jacobian":

1. the divisor-class group `Pic0` above — the object this note is about, used
   wherever the proof manipulates divisor classes
   ([math/009 §2](../math/009-hecke-jacobian-commute.md), where the Hecke
   correspondence acts on it);
2. the analytic comparison: a Hecke-equivariant injective additive monoid
   homomorphism `JZero N → S₂(Γ₀(N))^∨/Λ_N` onto the torsion,
   `exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice`
   ([Thm file, line 18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice.lean#L18)),
   which is a separate theorem with an Abel–Jacobi map and a period lattice;
3. the scheme-theoretic relative Jacobian
   `exists_relJacobian_jZero`
   ([Thm file, line 46](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_relJacobian_jZero.lean#L46)),
   used for Néron models and good reduction, not for the divisor-class
   arguments.

Keeping these apart is the main thing this section is for. The first is a group
of divisor classes defined by a quotient; the second is the statement that this
group agrees with the classical Jacobian up to the period lattice; the third is
the algebro-geometric Jacobian as a scheme. The proof uses all three, in
different places, and only the first is "divisors" in the sense of this note.

### The genus-one case, worked

The case where the Jacobian *is* the curve is worked out numerically in
[`../pymath/divisors_and_pic0.py`](../pymath/divisors_and_pic0.py), on
$`E : y^2 = x^3 - x`$ over $`\mathbb{F}_7`$. That curve has $`8`$ points and
$`E \cong \mathbb{Z}/2 \times \mathbb{Z}/4`$, with full rational
$`2`$-torsion; the demo's golden output is
[`../pymath/divisors_and_pic0.expected.txt`](../pymath/divisors_and_pic0.expected.txt),
written as an explanation rather than a computation. Here is the mathematics
behind it.

**Degrees and the residue theorem.** On the Weierstrass model the functions
$`x`$ and $`y`$ have divisors read off from the geometry:

$$x: \quad 2[(0,0)] - 2[O], \qquad
  y: \quad [(0,0)] + [(1,0)] + [(6,0)] - 3[O],$$

both of degree $`0`$: a nonzero function on a curve has as many zeros as poles.
The demo checks exactly that, and also that each divisor's points sum to $`O`$
in the group law — the genus-one case of §3's `HasPrincipalDivisors`
hypothesis. On an elliptic curve that condition is sharp: a degree-zero divisor
is principal precisely when its points sum to $`O`$.

**The group law is the divisor class group.** Let $`\ell`$ be the line through
$`P`$ and $`Q`$, and $`v`$ the vertical through $`P+Q`$. A line meets the curve
in three points counted with multiplicity, so
$`\mathrm{div}(\ell) = [P] + [Q] + [-(P+Q)] - 3[O]`$ and
$`\mathrm{div}(v) = [P+Q] + [-(P+Q)] - 2[O]`$; the quotient has divisor

$$[P] + [Q] - [P+Q] - [O] \;=\; \mathrm{div}(\ell) - \mathrm{div}(v),$$

which is principal, hence zero in $`\mathrm{Pic}^0`$. So $`[P] + [Q] = [P+Q]`$:
the addition law on the curve *is* addition of divisor classes. This is the
computation [math/009 §2](../math/009-hecke-jacobian-commute.md) generalizes,
where the same dictionary turns a correspondence of curves into a Hecke
operator on `Pic0`.

**The isomorphism, and the classification.** With $`\varphi(P) = [P] - [O]`$,
the identity above says $`\varphi(P) + \varphi(Q) = \varphi(P+Q)`$, so
$`\varphi`$ is a homomorphism; it is injective because $`[P] - [Q]`$ principal
forces $`P = Q`$; and $`\#E = \#\mathrm{Pic}^0 = 8`$, so it is bijective. More
generally the demo verifies that $`[P] + [Q] - [R] - [T]`$ is principal exactly
when $`P + Q = R + T`$: degree-zero divisors are classified, modulo principal
ones, by the group sum of their points. That classification is the genus-one
shadow of the general theory: `Pic0` is exactly the group of degree-zero
classes, and the input that makes it the honest class group — principal
divisors having degree zero — is the hypothesis `HasPrincipalDivisors` of §3.

**The demo's checks, against this note.** Its $`13`$ `check` lines fall into
the following groups: degree of the divisors of $`x`$ and $`y`$, and additivity
of degree — §2; the Abel–Jacobi sums, and "principal iff the points sum to $`O`$" — §3;
the chord–tangent divisor, $`\varphi(P) + \varphi(Q) = \varphi(P+Q)`$ and
injectivity — the paragraphs above; the distinctness of the eight classes and
the general criterion — §4. The demo's own §5 is a prose summary of this note's
§§2–4 in miniature, including both modular-curve uses: the Hecke action on
`Pic0`, and the Galois representation on its torsion.

## 5. The calculus on divisors: restriction, ramification, push and pull

Divisors are not used in isolation: the proof pushes and pulls them along the
degeneracy maps $`X_0(N\ell) \to X_0(N)`$. The code builds that calculus, and it
is a good illustration of how much of the arithmetic of a curve can be done
without a scheme.

**Restriction of a place.** For an inclusion of function fields $`F \subseteq F'`$
there is a place $`w \mapsto w|_F`$ of the smaller field, defined by intersecting
the local ring with $`F`$:

```lean
def restrict : Place K F
```

([Def_AlgebraicCurve_DivisorPushPull.lean, line 277](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L277)),
with `ord_restrict` giving the local formula
([line 293](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L293)):
the order at $`w`$ of a function from $`F`$ is the ramification index times its
order at the restriction,
and `restrict_fiber_finite` saying that only finitely many places of $`F'`$ lie
above a given place of $`F`$
([line 334](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L334)).
That finiteness is again a consequence of `HasPrincipalDivisors`, this time for
$`F'`$: the lemma carries it as a hypothesis, and the proof is that a function
with a pole at the restriction can only have its divisor supported at the places
above it.

**Ramification and inertia.** The two local invariants of the extension at a
place are its ramification index and its inertia degree:

```lean
def ramificationIndex (F : Type*) [Field F] [Algebra F F'] : ℕ
```
```lean
def inertiaDeg : ℕ := Module.finrank (w.restrict F).ResidueField w.ResidueField
```

([lines 135](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L135)
and [427](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L427)),
with the basic laws `ramificationIndex_pos`,
`exists_ord_eq_ramificationIndex` (the order at $`w`$ is the ramification index
times the order at the restriction), `ramificationIndex_dvd_ord`, and
`deg_restrict_mul_inertiaDeg`
([lines 154–429](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L154-L429)).
Where these are not provable for an arbitrary extension, the code packages the
missing input as a class: `FundamentalIdentity`
([line 611](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L611))
and `SumRamificationInertia`
([line 656](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L656)).
This is the same pattern as `HasPrincipalDivisors`: state the theorem for the
curve as a hypothesis, assume it where the curve is known.

**Pushforward and pullback.** A place of $`F'`$ maps to its restriction, and a
divisor of $`F'`$ can be pushed forward to $`F`$ by applying that map to the
support:

```lean
def mapRestrict : Divisor K F' →+ Divisor K F
```
```lean
def pushforward : Divisor K F' →+ Divisor K F
```

([lines 438](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L438)
and [448](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L448)),
with `degree_pushforward` and `pushforward_mem_degZero` saying that pushing
forward preserves degree and hence degree-zero divisors
([lines 459](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L459)
and [469](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L469)).
The pullback goes the other way: the fibre of a place is a finite set, and each
preimage contributes with its ramification index. First the fibre:

```lean
def fiber (v : Place K F) : Finset (Place K F')
```

([line 518](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L518)).
Then the contribution of a preimage, and the pullback it builds:

```lean
def pullbackSingleHom (v : Place K F) : ℤ →+ Divisor K F' where
  toFun n := ∑ w ∈ v.fiber F', Finsupp.single w (n * w.ramificationIndex F)

def pullback : Divisor K F →+ Divisor K F'
```

([lines 535–536](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L535-L536)
and [549](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L549)),
so pulling back $`n \cdot v`$ sums $`n\,e_w`$ over the places above $`v`$, where
$`e_w`$ is the ramification index.
with degree behaviour and degree-zero preservation available exactly under the
`FundamentalIdentity` hypothesis
([lines 618–634](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L618-L634)).
Finally the pullback descends to the class groups:

```lean
def pullbackHom [FundamentalIdentity K F F'] : Pic0 K F →+ Pic0 K F'
```

([line 697](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L697)).
This is the map the Hecke correspondence is built from: a divisor-level
correspondence is precisely a pair of maps between function fields, and the
Hecke operator is its action on `Pic0`.

**Galois action.** The last piece of the calculus is the action of the
automorphisms of $`F`$ over $`K`$ on places, and hence on divisors and class
groups. It is defined by transporting the local ring along the automorphism:

```lean
def smulRingEquiv (A : ValuationSubring F) : A ≃+* (σ • A : ValuationSubring F)
```
```lean
instance : SMul (F ≃ₐ[K] F) (Place K F)
```

([lines 262](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L262)
and [285](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L285)),
with the three fields of `Place` transported one by one. Because the action is
by ring isomorphisms, it carries the valuation, the order, the residue field and
the degree along; and because `Divisor` is a `Finsupp` and `Pic0` a quotient of
a subgroup, the action descends automatically. That descent is what §4's
`DistribMulAction` instance on `JZero N` is an instance of.

## 6. What else lives in this layer

The files surveyed above are the core; the proof also uses these neighbours,
listed so that the reader knows where to look and what each is for. None of them
changes the picture of §§1–3.

- **`GluedPic0`, `NodalPic0`** — the class group of a *singular* (nodal) fibre,
  where the local rings are no longer discrete valuation rings and the divisor
  theory has to be glued from the normalization. This is the fibre-side input to
  the degeneration arguments.
- **`Pic0BaseChange`, `Pic0Congr`** — functoriality of `Pic0` under base change
  and under isomorphisms of fields, i.e. how the group depends on the field it
  is defined over.
- **`FrobeniusEndo`, `FrobeniusEndoPic0`** — the Frobenius endomorphism on
  divisors and on `Pic0`, and the induced action on Hecke fibres.
- **`UniversalDivisor`, `RelCartier`** — relative effective divisors and the
  Cartier condition, which is where the divisor theory meets the
  scheme-theoretic side of the project (the third Jacobian of §4).
- **`HasCanonicalDivisor`, `canonicalDivisorOf`, `canonicalClass`, `genus`** —
  divisors of differentials. The canonical divisor is defined by the order of a
  nonzero Kähler differential,
  ```lean
  class HasCanonicalDivisor : Prop where
    exists_divisor : ∀ ω : Ω[F⁄K], ω ≠ 0 → ∃ D : Divisor K F,
      ∀ v : Place K F, D v = v.ordDifferential ω
  ```
  ([Def_AlgebraicCurve_CanonicalDivisor.lean, lines 14–17](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean#L14-L17)),
  with the Kähler differentials `Ω[F⁄K]` from mathlib
  ([Kaehler/Basic.lean, line 22](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Kaehler/Basic.lean#L22)),
  its class in `Pic` is `canonicalClass`
  ([line 27](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean#L27)),
  and the **genus** is read off its degree,
  ```lean
  def genus (K F : Type*) [Field K] [Field F] [Algebra K F]
      [HasCanonicalDivisor (K := K) (F := F)] : ℕ :=
    letI := Classical.propDecidable
    if h : ∃ ω : Ω[F⁄K], ω ≠ 0
    then (Divisor.degree (canonicalDivisorOf h.choose_spec) + 2).toNat / 2
    else 0
  ```
  ([lines 33–40](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean#L33-L40)).
  The `+ 2)/2` is $`g = (\deg K_F + 2)/2`$, the Riemann–Roch normalization of
  the canonical divisor; the genus is what §3's `AbelJacobiCard` counts with.
- **`ResidueTheorem` and the Riemann–Roch layer** — the theorems, for curves,
  that supply the hypotheses of §§3 and 5: degree-zero principal divisors, the
  finiteness of fibres, and the rows of the Riemann–Roch computation. They are
  where the analytic content of this note's hypotheses lives.

## 7. Key point → declaration map

| Mathematics | Lean declaration | Location |
|---|---|---|
| a closed point as a local ring | `Place` | [DivisorClassGroup 22–29](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L22-L29) |
| residue field and degree $`\deg v = [\kappa(v) : K]`$ | `Place.ResidueField`, `Place.deg` | [88–90](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L88-L90) |
| normalized order $`\mathrm{ord}_v`$ | `Place.ord` | [122](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L122) |
| divisors as finite $`\mathbb{Z}`$-combinations of places | `Divisor` | [179](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L179) |
| degree as a homomorphism | `Divisor.degree`, `degree_single` | [185–189](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L185-L189) |
| degree-zero divisors | `Divisor.degZero` | [193](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L193) |
| divisors of functions, and their closure laws | `Divisor.IsPrincipal`, `Divisor.principal` | [198–210](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L198-L210) |
| the residue theorem, as a hypothesis | `HasPrincipalDivisors` | [217–219](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L217-L219) |
| divisor classes, degree-zero divisor classes | `Pic`, `Pic0` | [221–225](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L221-L225) |
| torsion of `Pic0`, $`p`$-adic rank $`2g`$ | `Pic0.torsion`, `AbelJacobiCard` | [244–253](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L244-L253) |
| the Jacobian $`J_0(N)(\bar{\mathbb{Q}})`$ as divisor classes | `JZero` | [ArithmeticGalois 111–116](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ArithmeticGalois.lean#L111-L116) |
| the residue theorem for $`\bar{\mathbb{Q}}(X_0(N))`$ | `hasPrincipalDivisors_modularFunctionFieldBar` | [Thm 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean#L10) |
| every place over $`\bar{\mathbb{Q}}`$ has degree one | `deg_eq_one_modularFunctionFieldBar` | [Thm 12](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean#L12) |
| restriction of a place, finite fibres | `Place.restrict`, `restrict_fiber_finite` | [PushPull 277](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L277), [334](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L334) |
| ramification index and inertia degree | `ramificationIndex`, `inertiaDeg` | [135](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L135), [427](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L427) |
| the two missing inputs, as hypotheses | `FundamentalIdentity`, `SumRamificationInertia` | [611](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L611), [656](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L656) |
| pushforward and pullback, on divisors and on `Pic0` | `pushforward`, `pullback`, `pullbackHom` | [448](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L448), [549](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L549), [697](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L697) |
| Galois action on places, hence on divisors | `Place.smulRingEquiv` | [262](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L262) |
| canonical divisor, its class, the genus | `HasCanonicalDivisor`, `canonicalClass`, `genus` | [CanonicalDivisor 14–40](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean#L14-L40) |
| the analytic Jacobian comparison | `exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice` | [Thm 18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice.lean#L18) |
| the scheme-theoretic relative Jacobian | `exists_relJacobian_jZero` | [Thm 46](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_relJacobian_jZero.lean#L46) |

## 8. Lean detours (not mathematics)

Four encoding choices in this layer look arbitrary until one asks what breaks
without them.

- **`Finsupp` is the free abelian group.** Writing `Divisor K F` as
  `Place K F →₀ ℤ` rather than as a formal sum makes "finite support" a type
  invariant instead of a proof obligation: `D.support` is a `Finset`, every sum
  over it is finite, and `Finsupp.single`/`Finsupp.liftAddHom` give the
  universal property. The price is that every formula is phrased with
  `Finsupp.add_apply`-style rewrites, which is why the closure proofs in
  `principal` read the way they do.
- **Degrees: `ℕ` for a place, `ℤ` for a divisor.** `Place.deg` is a natural
  number, since a residue-field dimension is; `Divisor.degree` maps into
  `ℤ`, since coefficients can be negative. The coerced `(v.deg : ℤ)` in the
  definition of `degree` is the only trace of the mismatch.
- **Existence statements are `class`es.** `HasPrincipalDivisors`,
  `HasCanonicalDivisor`, `FundamentalIdentity` and `SumRamificationInertia` are
  all `class ... : Prop` with a single `exists_...` field. The point is not
  typeclass magic: it is that these are theorems about *curves* that are not
  provable for an arbitrary field extension, so they must appear in the
  hypotheses of every lemma that uses them. Making them classes lets a later
  file discharge them once and forget about them.
- **`addSubgroupOf`, not a kernel.** `Pic0` quotients `degZero` by
  `principal.addSubgroupOf degZero`, i.e. by the intersection with `degZero`,
  rather than by the kernel of a descended `degree` map. Both give the same
  group here, but only the first is available without proving that `degree`
  respects linear equivalence. It is a small instance of a recurring pattern in
  this project: choose the encoding that makes the quotient *exist* first, and
  prove the identification later if it is ever needed.

## 9. Links

FLT sources at the pinned sha `aa2d8b3`:

- [Def_AlgebraicCurve_DivisorClassGroup.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean) — `Place`, `ord`, `Divisor`, `degree`, `degZero`, `principal`, `HasPrincipalDivisors`, `Pic`, `Pic0`, torsion, `AbelJacobiCard`, the Galois action
- [Def_AlgebraicCurve_DivisorPushPull.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean) — `restrict`, `ramificationIndex`, `inertiaDeg`, `fiber`, `pushforward`, `pullback`, `pullbackHom`, `FundamentalIdentity`, `SumRamificationInertia`
- [Def_AlgebraicCurve_CanonicalDivisor.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean) — `HasCanonicalDivisor`, `canonicalClass`, `genus`
- [Def_ModularCurve_ArithmeticGalois.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ArithmeticGalois.lean) — `JZero`, and the Galois action on it
- [Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice.lean) — `JZero` versus $`S_2(\Gamma_0(N))^\vee/\Lambda_N`$
- [Thm_ModularCurve_exists_relJacobian_jZero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_relJacobian_jZero.lean) — the relative Jacobian

Mathlib at tag `v4.33.0`:

- [ValuationSubring.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Valuation/ValuationSubring.lean) — `ValuationSubring`
- [DedekindDomain/Ideal/Lemmas.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean) — `HeightOneSpectrum` and its valuation
- [LocalRing/ResidueField/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/LocalRing/ResidueField/Defs.lean) — `IsLocalRing.ResidueField`
- [Algebra/Group/Subgroup/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Group/Subgroup/Basic.lean) — `Subgroup.subgroupOf` and its additive form
- [LinearAlgebra/Dimension/Finrank.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/LinearAlgebra/Dimension/Finrank.lean) — `Module.finrank`
- [RingTheory/Kaehler/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Kaehler/Basic.lean) — the notation `Ω[S⁄R]`

Demos at the same revision:

- [pymath/divisors_and_pic0.py](../pymath/divisors_and_pic0.py) — the genus-one computation of §4, and its [golden output](../pymath/divisors_and_pic0.expected.txt)
- [pymath/README.md](../pymath/README.md) — the demo index, including the Riemann–Roch and Frobenius demos that continue this layer

Companion notes:

- [005 — Cyclic isogenies, congruence level, and the j-invariant](005-cyclic-isogenies-and-level.md) — the quotient dictionary and `Γ₀(N)` this note assumes
- [006 — The modular equation](006-the-modular-equation.md) — the function fields $`\mathbb{Q}(X_0(N))`$ on which these divisors live
- [007 — The Weil pairing](007-weil-pairing.md) — torsion of `E`, the Tate module, and the rank $`2g`$ that §3 states as `AbelJacobiCard`
- [math/009 §2](../math/009-hecke-jacobian-commute.md) — where the Hecke correspondence acts on `Pic0`
- [studies/hecke-commute-bar-survey.md §2](../studies/hecke-commute-bar-survey.md) — the survey of this layer that motivated the note
