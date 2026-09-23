# The rational function field and principal divisors

On a smooth projective curve, a nonzero function has as many zeros as poles,
counted with degree:

$$\deg \mathrm{div}(f) \\;=\\; 0.$$

This is the **residue theorem in divisor form**. It is a theorem about curves, not
a formal consequence of the definitions: for an arbitrary field extension it can
fail, and [008 §3](008-divisors-and-pic0.md) therefore states it as a hypothesis —
the class `HasPrincipalDivisors` — and records it as discharged for the modular
function field. This note explains *how* it is discharged, in the form the FLT
proof actually uses.

The argument is a two-step reduction. The **base case** is the rational function
field $`K(t)`$, i.e. the projective line: there the places are completely
explicit, and the divisor of a function can be written down and its degree
computed by unique factorization in $`K[t]`$. The **transfer** to a general
function field uses the norm: a function field $`F/K`$ is a finite extension of
some $`K(t)`$, the norm of a function of $`F`$ is a rational function, and the
divisor of the norm is the pushforward of the divisor — so degree zero on $`F`$
follows from degree zero on $`K(t)`$.

It assumes [015](015-places-and-extensions.md) (places, extensions, and the
fibre-centre dictionary) and [016 §5](016-correspondences-and-exchange.md) (the
norm formula). Line numbers pin `anthropics/fermats-last-theorem@aa2d8b3`;
mathlib citations point at tag v4.33.0.

## 1. The places of $`K(t)`$

**The field.** The rational function field is mathlib's `RatFunc K`, the fraction
field of $`K[X]`$, written $`K(t)`$ or $`K(X)`$. It is the function field of the
projective line $`\mathbb{P}^1_K`$, and its places come in exactly two kinds.

**Finite places.** Every irreducible polynomial
$`p \in K[X]`$ generates a maximal ideal $`(p)`$, hence a height-one prime of the
principal ideal domain $`K[X]`$, hence a place:

```lean
-- Def_AlgebraicCurve_RatFuncPlaces.lean, lines 98–121
def heightOneSpectrumOfIrreducible {p : K[X]} (hp : Irreducible p) : HeightOneSpectrum K[X] where
  asIdeal := Ideal.span {p}
  …
def finitePlace {p : K[X]} (hp : Irreducible p) : Place K (RatFunc K) :=
  Place.ofHeightOneSpectrum (heightOneSpectrumOfIrreducible K hp)
```

([lines 98–121](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean#L98-L121)).
Conversely every height-one prime of $`K[X]`$ is of this form
(`exists_irreducible_span`,
[line 108](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean#L108-L118)),
because $`K[X]`$ is a principal ideal domain. The residue field is
$`K[X]/(p)`$, and the degree is the polynomial degree:

$$\deg(\mathfrak{p}) \\;=\\; \deg p,$$

```lean
-- line 224
theorem deg_ofHeightOneSpectrum {w : HeightOneSpectrum K[X]} {p : K[X]}
    (hw : w.asIdeal = Ideal.span {p}) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).deg = p.natDegree
```

([line 224](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean#L224-L228)).
The proof identifies the residue field with $`K[X]/(p)`$ by an explicit
$`K`$-algebra isomorphism (`residueFieldEquivOfHeightOneSpectrum`,
[line 210](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean#L210-L222))
and invokes mathlib's `finrank_quotient_span_eq_natDegree`
([AdjoinRoot, line 727](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/AdjoinRoot.lean#L727)).
For a linear polynomial $`X - a`$ the residue field is $`K`$, so each
$`a \in K`$ gives a degree-one place, the point $`t = a`$:

```lean
-- lines 236 and 262
def placeOfPoint (a : K) : Place K (RatFunc K) := finitePlace K (irreducible_X_sub_C a)
theorem deg_placeOfPoint (a : K) : (placeOfPoint K a).deg = 1
```

([lines 236–263](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean#L236-L263)).

**The place at infinity.** The second kind of place is not a maximal ideal of
$`K[X]`$ at all; it is the valuation that measures the pole order at infinity,
and it is built directly from mathlib's `RatFunc.inftyValuation`:

```lean
-- Def_AlgebraicCurve_RatFuncPlaceInfty.lean, lines 25–36
def placeInfty : Place K (RatFunc K) :=
  haveI := nontrivial_valueGroup_inftyValuation K
  { toValuationSubring := (RatFunc.inftyValuation K).valuationSubring
    algebraMap_mem' := …
    ne_top' := …
    isPrincipalIdealRing' := (Valuation.valuationSubring_isDiscreteValuationRing
        (RatFunc.inftyValuation K)).toIsPrincipalIdealRing }
```

([lines 25–36](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaceInfty.lean#L25-L36)).
The statement requires a `[DecidableEq (RatFunc K)]` instance only to certify
that the value group is nontrivial — the mathematical content is the valuation
ring of $`\mathrm{inftyValuation}`$
([mathlib, line 81](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/RatFunc/Valuation.lean#L81)).
Its residue field is $`K`$, so it has degree one
(`deg_placeInfty`, [Thm, line 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty.lean#L13)),
and $`1/X`$ is a uniformizer.

**Ostrowski's theorem.** Every place of $`K(t)`$ is one of these. Mathlib's
statement is the classification of rank-one discrete valuations trivial on
$`K`$:

```lean
-- mathlib, NumberTheory/RatFunc/Ostrowski.lean, line 261
theorem valuation_isEquiv_infty_or_adic [DecidableEq (RatFunc K)] :
    Xor (v.IsEquiv (RatFunc.inftyValuation K))
      (∃! (u : HeightOneSpectrum K[X]), v.IsEquiv (u.valuation _))
```

([mathlib, line 261](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/RatFunc/Ostrowski.lean#L261)).
Translating from valuations to places via
`Place.isEquiv_adicValuation_of_valuationSubring_eq`
([line 41](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean#L41-L45))
gives the place-level classification

```lean
-- Def_AlgebraicCurve_RatFuncPlaceClassification.lean, line 44
theorem eq_ofHeightOneSpectrum_or_eq_placeInfty (v : Place K (RatFunc K)) :
    (∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w) ∨ v = placeInfty K
```

([line 44](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaceClassification.lean#L44-L52)).
Two consequences are used constantly, and they are worth naming separately:

- the places that are **not** finite form a **subsingleton** — there is at most
  one point at infinity
  (`subsingleton_setOf_forall_ne_ofHeightOneSpectrum`,
  [Thm, line 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum.lean#L7));
- there is **at least one** such place
  (`exists_forall_ne_ofHeightOneSpectrum`,
  [Thm, line 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum.lean#L7));
  together they say that any place that is not a finite place *is* the place at
  infinity (`toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum`,
  [Thm, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum.lean#L8)),
  which is what lets a computation branch once and for all into "finite place" or
  "the point at infinity".

Over an algebraically closed base the classification becomes a parametrization
of all places by $`K \cup \{\infty\}`$: `placeEquivOption` is an equivalence
between the places of $`K(t)`$ and `Option K`, sending $`a`$ to the place
$`t = a`$ and `none` to `placeInfty`
([lines 100–120](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaceClassification.lean#L100-L120)).
This is the algebraic form of $`\mathbb{P}^1(K) = K \cup \{\infty\}`$.

## 2. The order function on $`K(t)`$

**At a finite place.** Let $`\mathfrak{p} = (p)`$ with $`p`$ irreducible. The
order $`\mathrm{ord}_\mathfrak{p}(f)`$ is the multiplicity of $`p`$ in the
numerator of $`f`$ minus its multiplicity in the denominator, when $`f`$ is in
lowest terms, and $`\mathrm{ord}_\mathfrak{p}(p) = 1`$:

```lean
-- Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span.lean, line 8
theorem … .ord_ofHeightOneSpectrum_of_span (w : HeightOneSpectrum K[X]) {p : K[X]}
    (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord (algebraMap K[X] (RatFunc K) p) = 1
```

([Thm, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span.lean#L8)).
This is the normalization of [015 §2](015-places-and-extensions.md) —
a uniformizer has order one — and it is the only place where the finite place's
order is pinned down. The compatibility with the height-one valuation is
`ord_ofHeightOneSpectrum_eq_neg_log`
([Thm, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log.lean#L8)).

**At infinity.** The place at infinity measures the pole order of $`f`$ there,
which is the negation of the degree of the rational function:

$$\mathrm{ord}_\infty(f) \\;=\\; -\deg f,$$

```lean
-- Thm_…_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum.lean, line 8
theorem … .ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum (v : Place K (RatFunc K))
    (hv : ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w) {f : RatFunc K}
    (hf : f ≠ 0) : v.ord f = -f.intDegree
```

([Thm, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum.lean#L8)),
where $`\deg f = \mathrm{intDegree}\,f = \deg(\mathrm{num}\,f) -
\deg(\mathrm{denom}\,f)`$ is mathlib's `RatFunc.intDegree`
([mathlib, Degree.lean, line 40](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/RatFunc/Degree.lean#L40)).
A polynomial of degree $`n`$ has a pole of order $`n`$ at infinity; a constant
has none. The place at infinity has degree one
(`deg_eq_one_of_forall_ne_ofHeightOneSpectrum`,
[Thm, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum.lean#L8)).

**One theory, two descriptions.** The order at a finite place is $`-\log`$ of the
height-one valuation at $`\mathfrak{p}`$; the order at infinity is $`-\log`$ of
$`\mathrm{inftyValuation}`$; both are normalized discrete valuations of $`K(t)`$
trivial on $`K`$. Ostrowski's theorem is exactly the assertion that these are all
the normalized valuations, so §1 and §2 together give the full local theory of
the projective line.

## 3. Principal divisors on the projective line

**The divisor of an irreducible polynomial.** For an irreducible $`p`$ of degree
$`n`$, viewed as a function on $`\mathbb{P}^1`$,

$$\mathrm{div}(p) \\;=\\; [\mathfrak{p}] \\; - \\; n\\,[\infty]:$$

a simple zero at the point $`p = 0`$ and a pole of order $`n`$ at infinity. The
order computation is `single_add_single_apply_eq_ord`
([Sol, line 52](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.lean#L52-L90)),
which checks the three cases: the place $`(p)`$ itself, where the order is one by
§2; any other finite place, where $`p`$ is a unit so the order is zero; and
infinity, where the order is $`-n`$. Its degree is zero:

```lean
-- Sol, line 92
theorem degree_single_add_single … :
    Divisor.degree (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single vinf (-(p.natDegree : ℤ))) = 0
```

([Sol, line 92](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.lean#L92-L102)),
because $`\deg\mathfrak{p} = n`$ and $`\deg\infty = 1`$: the two contributions
$`1 \cdot n`$ and $`(-n) \cdot 1`$ cancel. This one-line degree computation is
the whole arithmetic content of the residue theorem on $`\mathbb{P}^1`$.

**General polynomials.** Split into irreducibles and add. The formal proof is
unique factorization in $`K[X]`$:

```lean
-- Sol, line 110
theorem solution (q : Polynomial K) : ∀ D : Divisor K (RatFunc K),
    (∀ v, D v = v.ord (algebraMap (Polynomial K) (RatFunc K) q)) → Divisor.degree D = 0
```

([Sol, line 110](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.lean#L110-L147)),
by `UniqueFactorizationMonoid.induction_on_prime` on $`q`$: the zero polynomial
forces $`D = 0`$; a unit contributes nothing because constants have order zero at
every place; and $`q = a \cdot p`$ splits the divisor as
$`\mathrm{div}(a) + \mathrm{div}(p)`$, whose degrees are zero by induction and by
the irreducible case. The polynomial degree computation
`degree_eq_zero_of_forall_eq_ord_algebraMap`
([Thm, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.lean#L8))
is the base-case engine.

**General rational functions.** Write $`f = g/h`$ in lowest terms. Then
$`\mathrm{div}(f) = \mathrm{div}(g) - \mathrm{div}(h)`$, and both summands have
degree zero by the polynomial case:

```lean
-- Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord.lean, line 8
theorem … .degree_eq_zero_of_forall_eq_ord {f : RatFunc K} (D : Divisor K (RatFunc K))
    (hD : ∀ v, D v = v.ord f) : Divisor.degree D = 0
```

([Thm, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord.lean#L8)).
The proof
([Sol, line 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord.lean#L16-L46))
splits $`f`$ into `num`/`denom`, builds the divisor of the denominator from
finiteness of support, observes $`\mathrm{div}(f) + \mathrm{div}(\mathrm{denom}) =
\mathrm{div}(\mathrm{num})`$ by additivity of the order, and applies the
polynomial case twice. This theorem is *not* a duplicate of the polynomial one —
it is a reduction to it — and the two are separately useful: the polynomial
version is what the induction produces, and the rational version is what a
function field element looks like.

**Finiteness of the support.** Only the finitely many irreducible factors of the
numerator or denominator, together with at most infinity, can have nonzero order,
so the support is finite:

```lean
-- Thm_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero.lean, line 7
theorem … .finite_setOf_ord_ne_zero {f : RatFunc K} (hf : f ≠ 0) :
    {v : Place K (RatFunc K) | v.ord f ≠ 0}.Finite
```

([Thm, line 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero.lean#L7)).
The proof takes the finite set of prime factors of `num` and `denom` and adds the
one point at infinity. This finiteness is what makes $`\mathrm{div}(f)`$ a
well-defined member of the type `Divisor K (RatFunc K)` — which is by definition a
finitely supported function — and it is used to build it, not to state it.

**The base case.** Combining the two halves:

```lean
-- Sol, line 16
theorem solution (K : Type*) [Field K] : HasPrincipalDivisors K (RatFunc K) :=
  ⟨fun f hf =>
    ⟨Finsupp.ofSupportFinite (fun v => v.ord f)
        (finite_setOf_ord_ne_zero hf),
      fun _ => rfl,
      degree_eq_zero_of_forall_eq_ord _ fun _ => rfl⟩⟩
```

([Sol, line 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors.lean#L16-L21),
exported as `RationalFunctionField.hasPrincipalDivisors`,
[Thm, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors.lean#L8)).
This is the residue theorem for $`\mathbb{P}^1`$: on the projective line every
nonzero rational function has as many zeros as poles, and it is proved by unique
factorization, with no geometric input.

## 4. Transfer to a general function field

**Every function field is a finite extension of a rational one.** A function
field $`F/K`$ of transcendence degree one is a finitely generated field
extension of $`K`$; choosing $`t \in F`$ transcendental over $`K`$, the extension
$`F/K(t)`$ is finite. This is the hypothesis of the transfer theorem:

```lean
-- Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc.lean, line 8
theorem … .hasPrincipalDivisors_of_finiteDimensional_ratFunc (K : Type*) [Field K] [CharZero K]
    (F' : Type*) [Field F'] [Algebra K F'] [Algebra (RatFunc K) F']
    [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F'] :
    HasPrincipalDivisors K F'
```

([Thm, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc.lean#L10)).
The presentation as an extension of `RatFunc K` is part of the statement: the
base case is available, and the transfer consumes it.

**The norm transfers the residue theorem.** Let $`f \in F'`$ be nonzero and let
$`D`$ be its divisor, $`D(w) = \mathrm{ord}_w(f)`$. Its support is finite, and
the norm $`N_{F'/K(t)}(f)`$ is a nonzero rational function. The norm formula of
[016 §5](016-correspondences-and-exchange.md) says

$$\mathrm{ord}_v\big(N_{F'/K(t)} f\big) \\;=\\;
  \sum_{w \mid v} f(w/v)\\,\mathrm{ord}_w(f),$$

which is exactly the statement that $`\mathrm{div}(N f)`$ is the pushforward of
$`D`$:

$$\mathrm{div}\big(N_{F'/K(t)} f\big) \\;=\\; \pi_{\ast} D.$$

Pushforward preserves degree ([016 §1](016-correspondences-and-exchange.md)), so

$$\deg D \\;=\\; \deg \pi_{\ast} D \\;=\\;
  \deg \mathrm{div}\big(N_{F'/K(t)} f\big) \\;=\\; 0,$$

the last equality being the base case of §3. The formal proof is a three-line
chain

```lean
-- Sol, lines 769–772
have h0 : Divisor.degree (Divisor.pushforward (RatFunc K) D) = 0 :=
  RationalFunctionField.degree_eq_zero_of_forall_eq_ord _ (fun v => …norm formula…)
rw [← Divisor.degree_pushforward (F := RatFunc K) D]
exact h0
```

([Sol, lines 769–773](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean#L769-L773)).
The norm formula is the only analytic input; everything else is
[015](015-places-and-extensions.md) and the base case.

**Finiteness in the extension.** A nonzero function of $`F'`$ is integral over the
local ring at all but finitely many places, so its divisor has finite support;
the general finiteness statement is
`finite_setOf_ord_ne_zero_of_finiteDimensional`
([Thm, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_finite_setOf_ord_ne_zero_of_finiteDimensional.lean#L10)),
proved by bounding the places with $`\mathrm{ord}_w(f) \neq 0`$ by a finite union
of fibres coming from the coefficients of the minimal polynomial of $`f`$.
Finiteness of support plus degree zero is exactly the content of
`HasPrincipalDivisors`.

**The hypotheses.** There is no separability hypothesis in the statement above,
only `[CharZero K]`. Two things are happening.

- In characteristic zero every finite extension is separable, so mathlib
  synthesizes `Algebra.IsSeparable` and `PerfectField` instances automatically.
- The `Ideal.relNorm` computation that proves the norm formula uses
  `PerfectField` of the residue field, which characteristic zero supplies via
  `PerfectField.ofCharZero` ([mathlib, line 306](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Perfect.lean#L306)).

The hypothesis can be dropped at the cost of assuming separability explicitly:
`hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable` has no
`[CharZero K]` but adds `[Algebra.IsSeparable (RatFunc K) F']`
([Thm, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.lean#L10)).
The naming is again inverted from expectation: the generic-sounding
`of_finiteDimensional_ratFunc` is the char-zero specialization, and the
`_of_isSeparable` name is the general statement. For the FLT route the
characteristic is zero throughout, so the short form is the one used.

**The transcendental and adjoin forms.** The statement actually applied to a
field presented by generators is phrased with $`t`$ explicit:

```lean
-- Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean, line 8
theorem … .hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*}
    [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F
```

([Thm, line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean#L9)).
The proof transports the `RatFunc K`-algebra structure across the
$`K`$-algebra isomorphism $`K(t) \cong K(x)`$ and applies the transfer. The
**adjoin form** then allows a finite set of integral generators to be adjoined:

```lean
-- Thm_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.lean, line 9
theorem … .hasPrincipalDivisors_adjoin_of_transcendental (K : Type*) [Field K] [CharZero K]
    {LF : Type*} [Field LF] [Algebra K LF] (x : LF) (hx : Transcendental K x) (T : Finset LF)
    (hT : ∀ t ∈ T, IsIntegral (IntermediateField.adjoin K ({x} : Set LF)) t) :
    HasPrincipalDivisors K (IntermediateField.adjoin K (insert x (T : Set LF)))
```

([Thm, line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.lean#L9)).
The integrality hypothesis is what makes the adjoined extension finite over the
rational subfield; the proof is the finiteness of `finiteDimensional_adjoin`
followed by the transcendental form
([Sol, lines 19–72](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.lean#L19-L72)).

**The alternative route.** The residue theorem can also be reached without the
relative norm, by a Galois-averaging argument: pass to a primitive element, take
the splitting field of its minimal polynomial (Galois over $`K(t)`$), and prove
degree zero there by averaging the divisor over the Galois group, using
$`\mathrm{div}(N f)`$ as the average and
[015 §3](015-places-and-extensions.md)'s fundamental identity to control the
degree; then descend along the tower. This is the route of
`hasPrincipalDivisors_of_finiteDimensional_of_isSeparable`
([Sol, line 158](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable.lean#L158)).
The norm route is the one the FLT proof takes, because the norm formula is
needed anyway in [016 §5](016-correspondences-and-exchange.md) for the
correspondence to descend to $`\mathrm{Pic}^0`$; the Galois route would reprove
that input a second time. The two proofs coexist in the repository, and the note
records the choice rather than the discarded alternative.

**What this discharges.** `HasPrincipalDivisors K F` is a class with one field:

```lean
-- Def_AlgebraicCurve_DivisorClassGroup.lean, lines 217–219
class HasPrincipalDivisors : Prop where
  exists_divisor : ∀ f : F, f ≠ 0 → ∃ D : Divisor K F,
    (∀ v : Place K F, D v = v.ord f) ∧ Divisor.degree D = 0
```

([lines 217–219](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L217-L219)).
Since `Divisor` is `Place →₀ ℤ`, finite support is a type-level invariant and does
not appear among the fields. The base case and the transfer together prove that
the class holds for every function field over a characteristic-zero field — in
particular for the modular function fields of the FLT route — so the objects of
[008 §3](008-divisors-and-pic0.md) are geometric rather than formal.

## 5. How the code says all this

The base case lives in three definition modules and a handful of short solution
files; the transfer lives in the two large
`S_AlgebraicCurve_hasPrincipalDivisors_*` files.

- [`Def_AlgebraicCurve_RatFuncPlaces.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean)
  owns the finite places: `heightOneSpectrumOfIrreducible`, `finitePlace`,
  `placeOfPoint`, the residue-field isomorphism and `deg_ofHeightOneSpectrum`. It
  also carries the general `Place`/valuation dictionary (`mem_iff_adicValuation_le_one`,
  `ord_eq_zero_iff_adicValuation_eq_one`, `Place.ofHeightOneSpectrum`
  injectivity) reused by [015](015-places-and-extensions.md).
- [`Def_AlgebraicCurve_RatFuncPlaceInfty.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaceInfty.lean)
  owns `placeInfty` and nothing else.
- [`Def_AlgebraicCurve_RatFuncPlaceClassification.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaceClassification.lean)
  owns Ostrowski's place-level corollary, the "at most one infinite place"
  statements, and the $`\mathrm{Place} \cong \mathrm{Option}\,K`$
  parametrization over an algebraically closed base.
- `P2M/Sol/S_AlgebraicCurve_RationalFunctionField_*.lean` holds the base-case
  proofs: finiteness of support, degree zero for polynomials (the unique
  factorization induction), degree zero for rational functions, and the package
  `HasPrincipalDivisors K (RatFunc K)`.
- `P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean`
  (and its `_finiteDimensional_ratFunc` and `_of_isSeparable` siblings) holds the
  transfer: finiteness in the extension, the norm formula, and the degree-zero
  conclusion.

Two encoding points are worth carrying away.

1. **Finiteness is not a field of the class.** `Divisor` is an `Finsupp`, so a
   divisor is finitely supported by construction. The separate finiteness
   theorems (`finite_setOf_ord_ne_zero` at the base, and
   `finite_setOf_ord_ne_zero_of_finiteDimensional` in general) are what allow the
   `Finsupp` to be *built*; a reader who sees "finite support" in the prose should
   look for those lemmas, not for a hypothesis.
2. **The duplicated declarations here are transport scaffolding, not the two
   degree-zero theorems.** The `P2M.Dup` declaration is
   `deg_ofHeightOneSpectrum`, whose public copy is in the definition module and
   whose solution-level re-proof is exported under the `P2M.Dup` name with a
   `#p2m_type_eq_warn` check
   ([Thm, line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum.lean#L9));
   `eq_ofHeightOneSpectrum_or_eq_placeInfty` is duplicated the same way. The two
   degree-zero theorems, by contrast, are *not* duplicates: the `algebraMap` one
   is the polynomial case and the other reduces a rational function to it. Only
   one copy of each mathematical fact has to be read; the duplication in this
   area is transport scaffolding around the place-definition layer.

### Key point → declaration map

| Mathematics | Lean declaration | Location |
|---|---|---|
| rational function field | `RatFunc K` | [mathlib Defs 67](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/RatFunc/Defs.lean#L67) |
| the place at infinity | `placeInfty`, `RatFunc.inftyValuation` | [PlaceInfty 25](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaceInfty.lean#L25-L40), [mathlib Valuation 81](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/RatFunc/Valuation.lean#L81) |
| finite places from irreducible polynomials | `heightOneSpectrumOfIrreducible`, `finitePlace`, `Place.ofHeightOneSpectrum` | [RatFuncPlaces 98](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean#L98-L124), [DivisorClassGroup 465](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L465-L478) |
| degree-one places $`t = a`$ | `placeOfPoint`, `deg_placeOfPoint` | [RatFuncPlaces 236–263](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean#L236-L263) |
| Ostrowski's classification | `RatFunc.valuation_isEquiv_infty_or_adic`, `eq_ofHeightOneSpectrum_or_eq_placeInfty` | [mathlib Ostrowski 261](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/RatFunc/Ostrowski.lean#L261), [RatFuncPlaceClassification 44](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaceClassification.lean#L44-L52) |
| non-finite places form at most one point | `subsingleton_setOf_forall_ne_ofHeightOneSpectrum` | [Thm 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum.lean#L7) |
| and at least one | `exists_forall_ne_ofHeightOneSpectrum`, `toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum` | [Thm 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum.lean#L7), [Thm 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum.lean#L8) |
| places over $`\bar K`$ ↔ $`\bar K \cup \{\infty\}`$ | `placeEquivOption` | [RatFuncPlaceClassification 100](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaceClassification.lean#L100-L120) |
| residue degree at a finite place | `deg_ofHeightOneSpectrum`, `finrank_quotient_span_eq_natDegree` | [RatFuncPlaces 224](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean#L224-L228), [mathlib AdjoinRoot 727](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/AdjoinRoot.lean#L727) |
| residue degree at infinity | `deg_eq_one_of_forall_ne_ofHeightOneSpectrum` | [Thm 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum.lean#L8) |
| order at a finite place | `ord_ofHeightOneSpectrum_of_span`, `ord_ofHeightOneSpectrum_eq_neg_log` | [Thm 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span.lean#L8), [Thm 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log.lean#L8) |
| order at infinity | `ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum` | [Thm 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum.lean#L8) |
| divisor of a polynomial | `degree_eq_zero_of_forall_eq_ord_algebraMap`, `single_add_single_apply_eq_ord` | [Thm 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.lean#L8), [Sol 52](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.lean#L52-L102) |
| divisor of a rational function | `degree_eq_zero_of_forall_eq_ord` | [Thm 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord.lean#L8) |
| finite support | `finite_setOf_ord_ne_zero` | [Thm 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero.lean#L7) |
| the base case | `RationalFunctionField.hasPrincipalDivisors` | [Thm 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors.lean#L8) |
| finite support in the extension | `finite_setOf_ord_ne_zero_of_finiteDimensional` | [Thm 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_finite_setOf_ord_ne_zero_of_finiteDimensional.lean#L10) |
| the local norm formula | `Place.ord_norm_eq_sum_fiberOver`, `relNorm_fiberCenter` | [Thm 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver.lean#L9), [Sol 1032](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Divisor_pushforwardNormFormula.lean#L1032) |
| norm of a principal ideal | `relNorm_span_singleton`, `count_normalizedFactors_span_singleton` | [Sol 1062](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Divisor_pushforwardNormFormula.lean#L1062), [Thm 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_count_normalizedFactors_span_singleton.lean#L10) |
| degree zero in a finite extension | `hasPrincipalDivisors_of_finiteDimensional_ratFunc` | [Thm 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc.lean#L10) |
| the transcendental form | `hasPrincipalDivisors_of_transcendental` | [Thm 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean#L9) |
| the adjoin form | `hasPrincipalDivisors_adjoin_of_transcendental` | [Thm 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.lean#L9) |
| the class being discharged | `HasPrincipalDivisors` | [DivisorClassGroup 217](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L217-L219) |

## 6. Links

FLT sources at the pinned sha `aa2d8b3`:

- [Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean) — the finite places, residue degrees, and the general valuation dictionary
- [Definitions/Def_AlgebraicCurve_RatFuncPlaceInfty.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaceInfty.lean) — `placeInfty`
- [Definitions/Def_AlgebraicCurve_RatFuncPlaceClassification.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaceClassification.lean) — Ostrowski's corollary and the $`\mathrm{Option}\,K`$ parametrization
- [Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean) — `HasPrincipalDivisors`, `Place.ofHeightOneSpectrum`
- [`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord.lean) — reduction from rational functions to polynomials
- [`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.lean) — the unique-factorization degree computation
- [`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors.lean) — the base case
- [`P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean) — the norm transfer
- [`P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable.lean) — the Galois-averaging alternative
- [`P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.lean) — the adjoin form

Mathlib at tag `v4.33.0`:

- [FieldTheory/RatFunc/Valuation.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/RatFunc/Valuation.lean) — `RatFunc.inftyValuation`
- [FieldTheory/RatFunc/Degree.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/RatFunc/Degree.lean) — `RatFunc.intDegree`, `num`, `denom`
- [NumberTheory/RatFunc/Ostrowski.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/RatFunc/Ostrowski.lean) — the classification of valuations on $`K(t)`$
- [RingTheory/AdjoinRoot.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/AdjoinRoot.lean) — `finrank_quotient_span_eq_natDegree`
- [RingTheory/Ideal/Norm/RelNorm.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Ideal/Norm/RelNorm.lean) — `Ideal.relNorm`, `relNorm_eq_pow_of_isMaximal`
- [FieldTheory/Perfect.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Perfect.lean) — `PerfectField.ofCharZero`
- [FieldTheory/Separable.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Separable.lean) — `Algebra.IsSeparable.of_integral`

Companion notes:

- [008 — Divisors, linear equivalence, and Pic⁰](008-divisors-and-pic0.md) §3, §8 — the residue theorem as a hypothesis and the class that discharges it
- [015 — Places and their extensions](015-places-and-extensions.md) — the fibre-centre dictionary and the fundamental identity
- [016 — Correspondences and the exchange lemma](016-correspondences-and-exchange.md) §5 — the norm formula used here
- [009 — Differentials, residues, and Riemann–Roch](009-differentials-residues-riemann-roch.md) — the residue theorem in its other forms
- [math/009 — The Hecke action on the Jacobian](../math/009-hecke-jacobian-commute.md) §5 — where principal divisors enter the Hecke argument

Background:

- H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Ch. I — the rational function field, its places, and the residue theorem.
- J.-P. Serre, *Algebraic Groups and Class Fields*, GTM 117, Springer 1988, Ch. I — divisors, the norm, and the degree map.
- R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer 1977, Ch. II §6, IV §2 — the projective line and morphisms of curves.
