# Places and their extensions

This is the fifteenth `base/` note. [008](008-divisors-and-pic0.md) develops the
dictionary "point of a curve = discrete valuation ring in its function field" for
a *single* field: the order of vanishing $`\mathrm{ord}_P`$, the residue field
$`\kappa(P)`$, the degree $`\deg P`$, divisors, and the calculus on them. That
dictionary is enough only as long as the field does not move. The FLT route moves
it constantly — every pullback and pushforward is taken along a finite extension
of function fields, and every such map is computed point by point over the fibre.
This note is the local theory of that move.

The one-sentence answer: **a place of $`F`$ splits into finitely many places of a
finite extension $`F'`$, and two numbers govern the splitting** — the
**ramification index** $`e(w/v)`$, which records how the uniformizer pulls apart,
and the **inertia degree** $`f(w/v)`$, which records how the residue field grows.
Their product $`e f`$ is the local degree, and the local degrees over one place sum
to the global degree $`[F' : F]`$:

$$[F' : F] \\;=\\; \sum_{w \\mid v} e(w/v)\\, f(w/v).$$

That *fundamental identity* is what makes divisors move: pullback multiplies
degree by $`[F':F]`$, pushforward preserves it, and both respect principal
divisors. When $`F'/F`$ is Galois the places over $`v`$ are a single orbit, so
$`e`$ and $`f`$ are constant on the fibre and the identity reads
$`r e f = [F':F]`$; when it is not, one keeps a *semilinear* action of
automorphisms that move the base. Both numbers are multiplicative in towers.

This is the input to the exchange lemma of
[016](016-correspondences-and-exchange.md). It assumes [008](008-divisors-and-pic0.md)
(the divisor dictionary, especially §5) and [001](001-field-extensions-and-galois-basics.md)
§4 (decomposition and inertia as subgroups).

Line numbers pin `anthropics/fermats-last-theorem@aa2d8b3`; mathlib citations
point at tag v4.33.0. Most of the definitions live in four modules of
`Definitions/`; the proofs of the numerical theorems live in `P2M/Sol/` and are
re-exported, statement-for-statement, by `Theorems/` wrappers. Where a
declaration is a `private` lemma of a solution file it is cited as such, because
that is where the mathematics is written.

## 1. Places, valuation rings, and the order function

**A place is a valuation ring.** For a field $`F`$ with a distinguished subfield
$`K`$ — the constants — a **place** of $`F`$ over $`K`$ is a discrete valuation
ring $`\mathcal{O} \subseteq F`$ with fraction field $`F`$, containing the image
of $`K`$, and not equal to $`F`$. In the code this is one structure with four
fields

```lean
-- Def_AlgebraicCurve_DivisorClassGroup.lean, lines 22–30
structure Place where
  toValuationSubring : ValuationSubring F
  algebraMap_mem' : ∀ a : K, algebraMap K F a ∈ toValuationSubring
  ne_top' : toValuationSubring ≠ ⊤
  isPrincipalIdealRing' : IsPrincipalIdealRing toValuationSubring
```

([lines 22–30](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L22-L30)).
The ring is a mathlib `ValuationSubring F` — a subring $`A`$ such that
$`x \in A`$ or $`x^{-1} \in A`$ for every nonzero $`x`$ — and the last field is
the discreteness. Mathlib then supplies the two consequences that are used
everywhere: $`A`$ is a local ring, and a principal ideal ring is a discrete
valuation ring, hence a principal ideal domain
(the two anonymous instances at [lines 71–76](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L71-L76)).

**The local data.** From those fields the code derives exactly the local
invariants of a point:

- the maximal ideal $`\mathfrak{m}`$ is the height-one prime
  `heightOneSpectrum` ([line 95](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L95));
- the **residue field** $`\kappa = \mathcal{O}/\mathfrak{m}`$ is
  `ResidueField` ([line 88](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L88)),
  an abbreviation for `IsLocalRing.ResidueField`;
- the **degree** is $`\deg P = [\kappa : K]`$, i.e.
  `deg := Module.finrank K ResidueField`
  ([line 90](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L90));
- the adic valuation $`\mathrm{adicValuation} : F \to \mathbb{Z}^\mathrm{m0}`$
  ([line 102](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L102)),
  the height-one prime's valuation with values in $`\mathbb{Z}`$ adjoined a zero.

**The order function.** The normalization is chosen so that a uniformizer has
order one:

$$\mathrm{ord}_P(f) \\;=\\; -\log\big(\mathrm{adicValuation}_P(f)\big),$$

`ord` ([line 122](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L122)),
where $`\log`$ is the isomorphism
$`\mathbb{Z}^\mathrm{m0} \cong \mathbb{Z} \cup \{\infty\}`$ taking
$`\exp(-1)`$ to $`1`$. A uniformizer
$`\pi`$ — any irreducible element of $`\mathcal{O}`$ — satisfies
$`\mathrm{ord}_P(\pi) = 1`$
([`ord_coe_irreducible`, line 145](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L145)),
and every nonzero $`f`$ has a unique expression

$$f \\;=\\; u \\cdot \pi^{\\,\mathrm{ord}_P(f)}, \qquad u \in \mathcal{O}^{\times},$$

`exists_unit_mul_zpow`
([line 163](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L163-L175)).
The order is additive, kills units, and inverts:

```lean
-- lines 130, 136, 149, 141
theorem ord_mul (hf : f ≠ 0) (hg : g ≠ 0) : v.ord (f * g) = v.ord f + v.ord g
theorem ord_inv (f : F) : v.ord f⁻¹ = -v.ord f
theorem ord_zpow (f : F) (n : ℤ) : v.ord (f ^ n) = n * v.ord f
theorem ord_coe_unit (u : v.toValuationSubringˣ) : v.ord ((u : …) : F) = 0
```

These four laws are exactly what makes `principal` an additive subgroup in
[008 §3](008-divisors-and-pic0.md).

**The uniqueness statement.** The sign convention above is a choice; what is
*not* a choice is that the order is recovered from the ring. Two forms are used:

- a $`\mathbb{Z}`$-valued valuation $`w`$ whose valuation ring is
  $`\mathcal{O}`$ and which sends a uniformizer to $`\exp(-1)`$ has
  $`v.\mathrm{ord}\, f = -\log (w f)`$ for all nonzero $`f`$
  (`ord_eq_neg_log_of_valuationSubring_eq`,
  [Thm, line 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_ord_eq_neg_log_of_valuationSubring_eq.lean#L7));
- any valuation at all with the same valuation ring is *equivalent* to the adic
  one (`isEquiv_adicValuation_of_valuationSubring_eq`,
  [line 41](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean#L41-L45)).

This is the formal content of "the order depends only on the place", and it is
what legitimizes every later computation that identifies an order by identifying
a ring.

**Membership dictionary.** The nonnegative locus of $`\mathrm{ord}_P`$ is exactly
the ring, and the positive locus is exactly the maximal ideal:

$$f \in \mathcal{O} \\iff 0 \le \mathrm{ord}_P(f),
  \qquad f \in \mathfrak{m} \\iff 0 \lt \mathrm{ord}_P(f),$$

for nonzero $`f`$ (`mem_iff_ord_nonneg`, `mem_of_ord_nonneg`,
`ord_nonneg_of_mem`;
[lines 448, 463, 471](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_CharLFrobeniusGeomLevel.lean#L448-L474)).
Constants have order zero, `ord_algebraMap`
([line 6](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_ord_algebraMap.lean#L6)),
which is also the statement that the valuation is trivial on $`K`$.

**The three faces.** The same data can be presented as a place (the valuation
ring), a height-one prime of the relevant Dedekind domain, an equivalence class
of $`K`$-trivial discrete valuations, or the normalized function
$`\mathrm{ord}_P`$. The code fixes the first as the type `Place` and provides
`Place.ofHeightOneSpectrum` as the bridge from the second; the equivalences are
the uniqueness statements above. When a curve is presented by a coordinate ring
$`R`$ with $`F = \mathrm{Frac}(R)`$, the points are the height-one primes of
$`R`$, and this is the form in which [017](017-rational-function-field-and-principal-divisors.md)
builds the places of $`K(t)`$.

## 2. Extending a place to a finite extension

**The integral closure.** Let $`F'/F`$ be a finite extension of function fields
and $`v`$ a place of $`F`$. The substitute for "the fibre of the map of curves
over the point $`v`$" is the **integral closure** of $`\mathcal{O}_v`$ in $`F'`$:

```lean
-- Def_AlgebraicCurve_PlacesOverDVR.lean, line 220
abbrev integralClosureAt : Type _ := integralClosure v.toValuationSubring F'
```

([line 220](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L220)).
Three instances make it the right object, and they are the three hypotheses one
expects from extension theory:

- it is a **Dedekind domain**
  ([line 222](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L222-L223));
- it has **fraction field** $`F'`$
  ([line 225](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L225-L226));
- it is a **finite** module over $`\mathcal{O}_v`$
  ([line 228](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L228-L229)).

Finiteness over a principal ideal domain forces the ring to be a principal ideal
domain too, and therefore a DVR is local with a *unique* nonzero prime: every
prime above $`\mathfrak{m}`$ yields exactly one place of $`F'`$. The integral
closure is thus the coordinate ring of the cover over the local ring of the
point, and its closed fibre is literally the fibre.

**Places over $`v`$ are primes over $`\mathfrak{m}`$.** The dictionary is built
in two mutually inverse directions. Given $`w`$ over $`v`$, the **centre** of
$`w`$ on a subring is the preimage of the maximal ideal along the natural map:

```lean
-- Def_AlgebraicCurve_PlacesOverDVR.lean, lines 103–104
def center (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) : Ideal R :=
  (IsLocalRing.maximalIdeal w.toValuationSubring).comap (chartHom w hw)
```

([lines 103–104](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L103-L104)).
It is prime ([line 106](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L106-L108)),
nonzero ([`center_ne_bot`, line 139](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L139-L155)),
and its membership test is the order test

$$r \in \mathrm{center}(w) \\iff 0 \lt \mathrm{ord}_w(r),$$

`mem_center_iff_ord_pos`
([line 117](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L117-L122)).
For the integral closure itself the centre of a place $`w`$ restricting to $`v`$
is the **fibre-centre prime**

```lean
-- line 284
def fiberCenter (hw : w.restrict F = v) : HeightOneSpectrum (integralClosureAt F' v)
```

([line 284](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L284-L285)),
which lies over $`\mathfrak{m}`$ (`fiberCenter_liesOver`,
[line 322](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L322-L340)).
Conversely a nonzero prime $`\mathfrak{P}`$ of the integral closure gives a place

```lean
-- line 348
def placeOfPrime (P : HeightOneSpectrum (integralClosureAt F' v)) : Place K F'
```

whose valuation ring is the local ring at $`\mathfrak{P}`$
([line 348](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L348-L368)),
and the two constructions are inverse:

```lean
-- line 422
def fiberEquiv :
    {w : Place K F' // w.restrict F = v} ≃ HeightOneSpectrum (integralClosureAt F' v)
```

([line 422](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L422-L428)).
The composite identity is `eq_of_fiberCenter_eq`
([line 408](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L408-L412)):
two places over the same $`v`$ with the same fibre-centre prime are equal.

**The fibre is finite, and the residue field is the quotient.** The fibre
$`\{w : w \mid v\}`$ is finite because the primes of a Dedekind domain over a
nonzero prime form a finite set (`finite_setOf_restrict_eq`,
[line 438](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L438-L449)),
and the code packages it as a `Finset`,

```lean
-- line 453
def fiberOver : Finset (Place K F')
```

([line 453](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L453-L458)),
with `card_fiberOver_eq` identifying its cardinality with the number of primes
over $`\mathfrak{m}`$
([line 471](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L471-L495)).
The residue field of $`w`$ is the quotient of the integral closure by the
fibre-centre prime, $`\kappa(w) = \mathcal{O}'/\mathfrak{P}`$; the
order of an element pulled back from the integral closure is governed by
`ord_algebraMap_integralClosureAt`
([line 315](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L315-L320)), which already contains the
factor $`e`$ of §3.

**The local picture.** Classically one completes: the fibre becomes
$`\widehat{F'}_v \cong \prod_{w \mid v} \widehat{F'}_w`$ over the local field
$`F_v`$, one factor per place above $`v`$, which is the dimensional reason the
fibre is finite and the local degrees add up. The project has a completion API
([`Def_AlgebraicCurve_PlaceCompletion.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlaceCompletion.lean)),
but the fibre statements used downstream are proved *without* it, directly from
the Dedekind factorization theory of the integral closure — the product
decomposition is the intuition, not the proof.

**Why the integral closure and not the field.** The field $`F'`$ alone knows
nothing about which places lie over $`v`$; the fibre is a property of the cover
over the local ring of the point, and the integral closure is precisely the
affine ring of that cover. Its ideals record the splitting, and its quotients are
the residue fields.

## 3. Ramification, inertia, and the fundamental identity

**Ramification index.** How does the uniformizer of $`v`$ pull apart over
$`w`$? The order $`\mathrm{ord}_w`$ can only grow, and the possible growth is the
set of positive orders of elements of $`F`$. The code defines $`e`$ as its
minimum:

```lean
-- Def_AlgebraicCurve_DivisorPushPull.lean, lines 135–136
def ramificationIndex (F : Type*) [Field F] [Algebra F F'] : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F' f) = n}
```

([lines 135–136](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L135-L136)).
For $`F'/F`$ integral the set is nonempty
([line 149](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L149-L152)),
so $`e \gt 0`$ ([line 154](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L154-L155)),
and it divides the order of *every* element pulled back from $`F`$
(`ramificationIndex_dvd_ord`,
[line 161](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L161-L189)).
The definition is minimality, not the classical
"exponent with $`\mathfrak{P}^e \parallel \pi\mathcal{O}'`$"; the two agree, and
the classical one is recovered in §3 below through the fibre-centre prime.

The central identity is $`\mathrm{ord}_w = e \cdot \mathrm{ord}_v`$ along the
structure map:

```lean
-- Def_AlgebraicCurve_DivisorPushPull.lean, lines 293–294
theorem ord_restrict (f : F) :
    w.ord (algebraMap F F' f) = ramificationIndex (F := F) w * (w.restrict F).ord f
```

([line 293](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L293-L325)).
So $`e`$ is not merely the order of a uniformizer: it is the exact conversion
factor between the two order functions on the image of $`F`$. Equivalently, if
$`\pi`$ is a uniformizer of $`v`$ then $`\mathrm{ord}_w(\pi) = e`$, and
$`\mathfrak{m}_v \mathcal{O}_w = \mathfrak{m}_w^{e}`$ — the exponent is the same
number.

**Inertia degree.** The residue field grows by a finite degree

```lean
-- Def_AlgebraicCurve_DivisorPushPull.lean, line 427
def inertiaDeg : ℕ := Module.finrank (w.restrict F).ResidueField w.ResidueField
```

([line 427](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L427)),
and the two invariants together account for the degree of the point:

```lean
-- line 429
theorem deg_restrict_mul_inertiaDeg : (w.restrict F).deg * w.inertiaDeg F = w.deg
```

([line 429](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L429-L430)),
i.e. $`f(w/v) \cdot \deg v = \deg w`$, which is the multiplicativity of the
residue degree in a tower of fields $`K \subseteq \kappa(v) \subseteq \kappa(w)`$.

**The dictionary with the integral closure.** The two invariants are the
ramification index and inertia degree attached to the fibre-centre prime:

- $`e(w/v)`$ equals `Ideal.ramificationIdx'` of $`\mathfrak{P}`$ over
  $`\mathfrak{m}_v`$ (`ramificationIndex_eq_ramificationIdx_fiberCenter`,
  [Sol, line 176](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean#L176-L204)),
  proved from the equivalence
  $`n \le \mathrm{ord}_w(c) \iff c \in \mathfrak{P}^n`$
  (`le_ord_iff_mem_pow_fiberCenter`,
  [Sol, line 153](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean#L153-L174))
  and `Ideal.ramificationIdx_spec`;
- $`f(w/v)`$ equals `Ideal.inertiaDeg'` of $`\mathfrak{P}`$ over
  $`\mathfrak{m}_v`$ (`inertiaDeg_eq_inertiaDeg_fiberCenter`,
  [Sol, line 347](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean#L347-L376)),
  through the isomorphism
  $`\mathcal{O}'/\mathfrak{P} \cong \kappa(w)`$ and the standard
  `Ideal.inertiaDeg_algebraMap`.

This is the technical heart of the note: it is what lets every fibre statement be
an instance of mathlib's ideal theory over the Dedekind domain
$`\mathcal{O}'`$.

**The fundamental identity.** Summing the local degrees gives the global degree:

```lean
-- Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean, line 9
theorem … .sum_ramificationIndex_mul_inertiaDeg_fiberOver … (v : Place K F) :
    ∑ w ∈ v.fiberOver F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)
      = (Module.finrank F F' : ℤ)
```

([Thm, line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean#L9)),
for $`F'/F`$ finite and separable. The proof is one line of bookkeeping after the
dictionary: rewrite the fibre sum as the sum over the primes of
$`\mathcal{O}'`$ lying over $`\mathfrak{m}_v`$, identify each term with
$`\mathrm{ramificationIdx}' \cdot \mathrm{inertiaDeg}'`$, and apply mathlib's
`Ideal.sum_ramification_inertia` — the theorem now named
`Ideal.sum_ramification_inertia_eq_finrank` in the newer
`RingTheory/RamificationInertia/Basic.lean`
([Sol, lines 384–422](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean#L384-L422)).

The code also bundles the identity as classes, so that downstream results can
take it as a hypothesis rather than re-derive it. `SumRamificationInertia` is the
clean form above ([line 656](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L656-L659));
`FundamentalIdentity` is the degree-weighted form

$$\sum_{w \mid v} e(w/v)\\, \deg w \\;=\\; [F':F] \cdot \deg v,$$

([line 611](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L611-L614)),
and an instance derives it from `SumRamificationInertia` using
$`\deg w = \deg v \cdot f`$
([line 661](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L661-L679)).
The two are interchangeable; which one a lemma assumes is a matter of taste.

**What it buys on divisors.** With the identity in hand the calculus of
[008 §5](008-divisors-and-pic0.md) is immediate:

- pushforward along $`F'/F`$ adds multiplicities weighted by $`f`$ and preserves
  degree, `degree_pushforward`
  ([line 459](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L459-L467));
- pullback distributes a point over the fibre weighted by $`e`$ and multiplies
  degree by $`[F':F]`$ under `FundamentalIdentity`, `degree_pullback`
  ([line 627](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L627-L632));
- both send principal divisors to principal divisors
  (`isPrincipal_pullback`,
  [line 598](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L598-L601);
  for pushforward this needs the norm formula of
  [016 §5](016-correspondences-and-exchange.md));
- hence both descend to $`\mathrm{Pic}^0`$, as `pullbackHom`
  ([line 697](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L697-L705))
  and `pushforwardHom`
  ([line 721](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L721-L731)).

**Unramified places.** A place is **unramified** when $`e = 1`$: the fibre can
still have several points, and then $`f = [F':F]`$ requires the fibre to be a
single point. The general shape to remember is $`r \cdot e \cdot f = [F':F]`$ in
the Galois case of §4; an unramified fibre is one where all the splitting is
inertial.

## 4. Galois and semilinear equivariance

**The group that acts.** When $`F'/F`$ is Galois, its automorphisms over $`F`$
act on the places over a fixed $`v`$. But the project needs a group that also
makes sense when $`F'/F`$ is *not* normal, and the right one is pairs of
automorphisms that move the base compatibly:

```lean
-- Def_AlgebraicCurve_BaseChangeGalois.lean, lines 15–16
def SemilinearAut : Subgroup (RingAut F × RingAut K) where
  carrier := {p | ∀ a : K, p.1 (algebraMap K F a) = algebraMap K F (p.2 a)}
```

([lines 15–24](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean#L15-L24)).
So $`g \in \mathrm{SemilinearAut}(K, F)`$ is a pair
$`(\sigma, \tau)`$ of ring automorphisms of $`F`$ and $`K`$ with

$$\sigma(\mathrm{algebraMap}\\, a) \\;=\\; \mathrm{algebraMap}(\tau a),$$

`toRingAut`/`baseAut`/`commutes`
([lines 34–40](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean#L34-L40)).
The $`K`$-linear automorphisms are the special case where the base part is
trivial, embedded by `ofAlgAut`
([line 76](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean#L76-L79)).

**The action on places.** The group acts on `Place K F` by transporting the
valuation ring:
$`(g \cdot v).\mathcal{O} = \sigma(\mathcal{O})`$
([line 120](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean#L120-L134)),
and the action preserves everything local:

$$(g \cdot v).\mathrm{ord}\\,(\sigma f) \\;=\\; v.\mathrm{ord}\\, f,
  \qquad (g \cdot v).\deg \\;=\\; v.\deg,$$

`ord_smul` ([line 151](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean#L151-L171))
and `deg_smul` ([line 190](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean#L190-L193)),
the latter through an explicit residue-field isomorphism
$`\kappa(v) \cong \kappa(g \cdot v)`$ that intertwines the structure maps by
$`\mathrm{baseAut}\, g`$
([line 173](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean#L173-L188)).
The action extends to divisors by permuting the points and preserves their
degree and principality
([lines 203–246](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean#L203-L246)),
hence descends to $`\mathrm{Pic}^0`$
([line 258](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean#L258-L285));
this is the $`K`$-linear action of [008 §8](008-divisors-and-pic0.md) in the
special case $`\tau = 1`$, generalized.

**Galois transitivity.** Suppose $`M/F'`$ is finite and Galois. Then the places
of $`M`$ over a fixed place of $`F'`$ form a single orbit:

```lean
-- Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean, line 10
theorem … .exists_algEquiv_smul_eq_of_restrict_eq (W W' : Place K M)
    (h : W'.restrict F' = W.restrict F') :
    ∃ σ : M ≃ₐ[F'] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W = W'
```

([Thm, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean#L10)).
The proof is short and worth recording, because it is where the fibre-centre
dictionary is actually used: send `W` and `W'` to the primes
$`\mathfrak{P}`$, $`\mathfrak{P}'`$ of the integral closure, which both lie over
$`\mathfrak{m}_{F'}`$; mathlib's Galois action on primes over a prime gives
$`\sigma`$ with $`\mathfrak{P}' = \sigma \cdot \mathfrak{P}`$
(`Ideal.exists_smul_eq_of_isGaloisGroup`); then `eq_of_fiberCenter_eq` turns the
equality of primes back into the equality of places
([Sol, lines 51–82](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean#L51-L82)).

**Constancy of $`e`$ and $`f`$.** Because the group acts by ring isomorphisms
compatible with the structure map, it fixes both invariants. The formal
statement is `IntertwinesAlong`: $`g'`$ on the big field intertwines with $`g`$ on
the small one along $`\mathrm{algebraMap}`$
([Correspondence, line 324](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L324-L325)),
the equivariance lemmas are stated for intertwining pairs
(`SemilinearAut.ramificationIndex_smul`,
[Thm, line 6](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_SemilinearAut_ramificationIndex_smul.lean#L6);
`SemilinearAut.inertiaDeg_smul`,
[Thm, line 6](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_SemilinearAut_inertiaDeg_smul.lean#L6)),
and the Galois consequences are

```lean
-- Thm_…_ramificationIndex_eq_of_restrict_eq.lean, line 9
theorem … .ramificationIndex_eq_of_restrict_eq (W W' : Place K M)
    (h : W'.restrict F' = W.restrict F') : W'.ramificationIndex F' = W.ramificationIndex F'
```

and likewise `inertiaDeg_eq_of_restrict_eq`
([line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq.lean#L9)).
Hence the fundamental identity collapses, in the Galois case, to the orbit-size
form

```lean
-- Thm_…_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg.lean, line 10
theorem … .card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (w : Place K F') (W : Place K M)
    (hW : W.restrict F' = w) :
    (w.fiberOver M).card * (W.ramificationIndex F' * W.inertiaDeg F') = Module.finrank F' M
```

([Thm, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg.lean#L10)):
on a Galois fibre, $`r \cdot e \cdot f = [M:F']`$.
[016 §4](016-correspondences-and-exchange.md) uses this form, not the general
sum.

**Decomposition and inertia, and 001 §4.** The stabilizer of $`W`$ in
$`\mathrm{Gal}(M/F')`$ is the **decomposition group**, and the kernel of its
action on $`\kappa(W)`$ is the **inertia subgroup**. In the Galois case the
orbit-stabilizer count identifies them numerically:

$$e(W/F') = |I|, \qquad f(W/F') = |D/I|, \qquad |D| = e f, \qquad
  r = [\mathrm{Gal} : D].$$

This is where the abstract subgroups of
[001 §4](001-field-extensions-and-galois-basics.md) acquire their arithmetic
meaning: the subgroup language is the local language. Nothing in 016 needs the
subgroups by name — the orbit and index lemmas
(`MulAction.ncard_orbit_inter_orbit_mul_card`,
`Subgroup.exists_eq_mul_of_index_inf_eq`) play their role — but this dictionary
is why the group-theoretic phrasing is the right one.

**The non-normal case.** If $`F'/F`$ is separable but not normal, the
$`F`$-automorphisms of $`F'`$ can be trivial, and there is no Galois action to
exploit. The remedy is to pass to a normal closure: embed $`F'`$ in
$`\overline{F}`$, take the normal closure $`E`$ of $`F'`$ over $`F`$ inside it,
and let $`\mathrm{SemilinearAut}(K, E)`$ act. An automorphism of $`E`$ need not
preserve $`F'`$, so it does not induce an automorphism of $`F'`$ — it *moves the
base* — and that is exactly what the semilinear formalism accommodates: it maps
a place of $`E`$ to another place while twisting the constants by
$`\mathrm{baseAut}`$, and it preserves $`\mathrm{ord}`$, $`\deg`$, $`e`$, $`f`$ by
§4's equivariance lemmas. Transitivity becomes "the places above a common place
are one orbit for the group coming from the closure", and the numerical facts are
transported back down using the tower multiplicativity of $`e`$ and $`f`$ — which
is [016 §4](016-correspondences-and-exchange.md)'s normal-closure reduction, and
the reason 015 and 016 are adjacent notes.

**Multiplicativity in towers.** For $`F \subseteq E \subseteq F'`$ with
$`w`$ a place of $`F'`$ and $`w' = w|_E`$,

$$e(w/v) \\;=\\; e(w/w')\\, e(w'/v), \qquad
  f(w/v) \\;=\\; f(w/w')\\, f(w'/v),$$

`ramificationIndex_eq_mul_ramificationIndex_restrict` and
`inertiaDeg_eq_mul_inertiaDeg_restrict`
([Sol, lines 68 and 81](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L68-L89)).
In the along-a-map language they are `Place.ramificationIndexAlong_comp` and
`Place.inertiaDegAlong_comp`
([line 6](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp.lean#L6),
[line 6](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_inertiaDegAlong_comp.lean#L6)).
These are the identities that let a computation at one level be compared with a
computation at another, and they are used exactly once in the exchange proof: to
replace a local degree $`e_F(W) f_F(W)`$ by a product of a quantity over the roof
and a quantity over the base, so that a common factor cancels. That cancellation
is the whole content of §4 of [016](016-correspondences-and-exchange.md).

## 5. The fibre over a place, intrinsically

The fibre can be described in two ways, and the difference matters for the
order in which results become available.

- **As places restricting to $`v`$**: `fiberOver` is the finite set
  $`\{w : \mathrm{restrict}\, w = v\}`$, obtained from the finiteness of the
  integral closure's primes over $`\mathfrak{m}_v`$
  ([line 453](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L453-L458)).
  It needs only that $`F'/F`$ is finite, separable and integral — no knowledge of
  principal divisors.
- **As the divisor-level fibre of 008 §5**: `fiber` is the same set, but its
  finiteness is derived from the finiteness of the support of a principal divisor
  ([DivisorPushPull, line 518](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L518-L524)),
  so it carries a `HasPrincipalDivisors K F'` hypothesis. The two agree when that
  hypothesis holds: `fiber_eq_fiberOver`
  ([PlacesOverDVR, line 497](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L497-L498)).

The class-free description is the one the project uses for local work, and this
is not a cosmetic choice. The exchange lemma of
[016](016-correspondences-and-exchange.md) must be proved *before* the norm
formula that shows pushforward preserves principal divisors, and therefore before
`HasPrincipalDivisors` is available for the roof field. Using `fiberOver` — a
statement about the integral closure of a DVR, requiring nothing of divisors —
is what makes the reduction to a single place legitimate at that stage. The
divisor-level `fiber` is then identified afterwards, when the class hypothesis
has been earned.

The bijection `fiberEquiv` of §2 is the precise sense in which "places above
$`v`$" and "maximal ideals of the integral closure" are the same data, and it is
compatible with order, residue field and degree through the dictionary of §3.

## 6. How the code says all this

The theory is spread over four definition modules and their solution files, and
the organization follows the mathematics closely.

- [`Def_AlgebraicCurve_DivisorClassGroup.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean)
  owns `Place`, its derived local data, the order function and its laws, and the
  divisor/`Pic`/`Pic0` types of 008.
- [`Def_AlgebraicCurve_DivisorPushPull.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean)
  owns `restrict`, `ramificationIndex`, `inertiaDeg`, the pushforward and
  pullback homomorphisms, the `FundamentalIdentity`/`SumRamificationInertia`
  classes, and the descent to `Pic0`.
- [`Def_AlgebraicCurve_PlacesOverDVR.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean)
  owns `integralClosureAt`, the centre and fibre-centre prime, the bijection
  `fiberEquiv`, and the class-free fibre `fiberOver`.
- [`Def_AlgebraicCurve_BaseChangeGalois.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean)
  owns `SemilinearAut`, its action on places, divisors and `Pic0`, and the
  torsion representation of §4.

The numerical theorems — the dictionary with `ramificationIdx'`/`inertiaDeg'`,
the fundamental identity, and the Galois constancy — are *not* in the definition
modules. Each is proved in a `P2M/Sol/S_*.lean` file, whose interesting content
is a chain of `private` lemmas, and re-exported statement-for-statement by a
`Theorems/Thm_*.lean` wrapper. A reader who follows a `Theorems/` link and finds
only a three-line file should open the `P2M/Sol/` file it imports: that is where
the argument is. The key-point table below gives both when the distinction
matters.

Four encoding details are worth carrying away.

1. **Everything is "along a map".** A field homomorphism $`\varphi : F \to F'`$
   over $`K`$ is turned into an `Algebra F F'` structure by `algebraAlong`, and
   the side conditions are bundled as the predicates `FiniteAlong`,
   `SeparableAlong`, `FundamentalIdentityAlong` and `NormFormulaAlong`
   ([Correspondence, lines 14–53](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L14-L53)).
   `Place.restrictAlong`, `Place.ramificationIndexAlong` and
   `Place.inertiaDegAlong` are the map-level spellings of `restrict`,
   `ramificationIndex` and `inertiaDeg`
   ([lines 204–220](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L204-L220)).
   This is the vocabulary [016](016-correspondences-and-exchange.md) uses
   throughout; in this note the two spellings are the same mathematics.
2. **The order dictionary is shipped twice.** The basic equivalence
   $`f \in \mathcal{O} \iff 0 \le \mathrm{ord}(f)`$ exists both as a public
   theorem and, under the name `P2M.Dup.AlgebraicCurve.Place.mem_iff_ord_nonneg`,
   as a wrapper that a `#p2m_type_eq_warn` pragma checks against the original
   ([Thm, line 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_mem_iff_ord_nonneg.lean#L7-L8)).
   The duplication is deliberate transport scaffolding, not two facts.
3. **Separability is a real hypothesis.** The fundamental identity
   (`FiniteDimensional` plus `Algebra.IsSeparable`) and the Galois constancy
   ($`IsGalois`$ at the roof) are where separability enters. For function fields
   over a characteristic-zero base it is automatic, which is why the FLT
   applications never have to think about it; the lemmas state it because they
   are field-theoretic, not arithmetic.
4. **Junk values are explicit conventions.** `ord 0 = 0` and `ord 1 = 0` by
   definition — the logarithm of the zero valuation is zero — so
   `ord_algebraMap` is unconditional. `ramificationIndex` is an `sInf` over
   $`\mathbb{N}`$ and is $`0`$ when its defining set is empty, which is why
   `ramificationIndex_pos` and `ord_restrict` carry an integrality hypothesis.
   And `deg = finrank` is $`0`$ when the residue field is infinite-dimensional
   over $`K`$: the `FiniteResidue` class on a place, and `IsCurveOver`'s
   `finiteResidue` field, exist precisely to rule that out. The FLT
   applications are in the regime where all three conventions are invisible.

### Key point → declaration map

| Mathematics | Lean declaration | Location |
|---|---|---|
| place as a valuation subring | `Place` | [DivisorClassGroup 22–30](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L22-L30) |
| place extensionality | `Place.ext`, `toValuationSubring_injective` | [60–67](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L60-L67) |
| discrete valuation ring and PIR instances (anonymous) | `IsDiscreteValuationRing v.toValuationSubring`, `IsPrincipalIdealRing v.toValuationSubring` | [71–76](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L71-L76) |
| residue field and degree | `Place.ResidueField`, `Place.deg` | [88–90](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L88-L90) |
| height-one prime, adic valuation, order | `Place.heightOneSpectrum`, `Place.adicValuation`, `Place.ord` | [95](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L95), [102](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L102), [122](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L122) |
| order laws | `Place.ord_mul`, `ord_inv`, `ord_zpow`, `ord_coe_unit` | [130–151](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L130-L151) |
| unit times uniformizer | `Place.exists_unit_mul_zpow`, `ord_coe_irreducible` | [145](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L145-L147), [163](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L163-L175) |
| order vs valuation | `ord_eq_neg_log_of_valuationSubring_eq`, `isEquiv_adicValuation_of_valuationSubring_eq` | [Thm 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_ord_eq_neg_log_of_valuationSubring_eq.lean#L7), [RatFuncPlaces 41](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean#L41-L45) |
| order-membership dictionary | `Place.mem_iff_ord_nonneg`, `mem_of_ord_nonneg`, `ord_nonneg_of_mem` | [CharLFrobeniusGeomLevel 448–474](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_CharLFrobeniusGeomLevel.lean#L448-L474) |
| order of constants | `Place.ord_algebraMap` | [Thm 6](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_ord_algebraMap.lean#L6) |
| integral closure at a place | `integralClosureAt` + Dedekind/fraction-ring/finite instances | [PlacesOverDVR 220–229](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L220-L229) |
| centre of a place | `Place.center`, `mem_center_iff_ord_pos`, `center_ne_bot` | [103](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L103-L108), [117](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L117-L122), [139](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L139-L155) |
| fibre-centre prime | `Place.fiberCenter`, `mem_fiberCenter_iff_ord_pos`, `fiberCenter_liesOver` | [284](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L284-L291), [322](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L322-L340) |
| places above $`v`$ ↔ primes of the integral closure | `Place.placeOfPrime`, `fiberEquiv`, `eq_of_fiberCenter_eq` | [348](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L348-L368), [408](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L408-L412), [422](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L422-L428) |
| the fibre as a finite set | `Place.fiberOver`, `mem_fiberOver`, `card_fiberOver_eq` | [453](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L453-L458), [471](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean#L471-L495) |
| restriction of a place | `Place.restrict`, `ord_restrict`, `mem_restrict_iff` | [DivisorPushPull 277](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L277-L291), [293](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L293-L325) |
| ramification index | `Place.ramificationIndex`, `ramificationIndex_pos`, `ramificationIndex_dvd_ord` | [135](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L135-L136), [154](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L154-L155), [161](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L161-L189) |
| inertia degree | `Place.inertiaDeg`, `deg_restrict_mul_inertiaDeg` | [427](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L427-L430) |
| ramification dictionary | `le_ord_iff_mem_pow_fiberCenter`, `ramificationIndex_eq_ramificationIdx_fiberCenter` | [Sol 153](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean#L153-L204) |
| residue dictionary | `inertiaDeg_eq_inertiaDeg_fiberCenter` | [Sol 347](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean#L347-L376) |
| fundamental identity | `sum_ramificationIndex_mul_inertiaDeg_fiberOver`, `Ideal.sum_ramification_inertia` | [Thm 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean#L9) |
| the identity as a class | `FundamentalIdentity`, `SumRamificationInertia` | [DivisorPushPull 611](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L611-L614), [656](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L656-L679) |
| pushforward and pullback on divisors | `Divisor.pushforward`, `Divisor.pullback`, `degree_pushforward`, `degree_pullback` | [448](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L448-L467), [549](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L549-L565), [459](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L459-L467), [627](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L627-L632) |
| descent to $`\mathrm{Pic}^0`$ | `Pic0.pullbackHom`, `Pic0.pushforwardHom` | [697](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L697-L705), [721](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L721-L731) |
| semilinear automorphisms | `SemilinearAut`, `toRingAut`, `baseAut`, `ofAlgAut` | [BaseChangeGalois 15–88](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean#L15-L88) |
| action on places | `SemilinearAut.instSMul…Place`, `smul_toValuationSubring` | [120–149](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean#L120-L149) |
| equivariance of order and degree | `Place.ord_smul`, `Place.deg_smul` | [151](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean#L151-L193) |
| action on divisors and $`\mathrm{Pic}^0`$ | `SemilinearAut.instDistribMulAction…Divisor`, `…Pic0`, `smul_mem_principal` | [203–285](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean#L203-L285) |
| places above $`v`$ in one orbit | `Place.exists_algEquiv_smul_eq_of_restrict_eq` | [Thm 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean#L10) |
| equivariance of $`e`$ and $`f`$ | `ramificationIndex_eq_of_restrict_eq`, `inertiaDeg_eq_of_restrict_eq` | [Thm 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_ramificationIndex_eq_of_restrict_eq.lean#L9), [Thm 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq.lean#L9) |
| Galois constancy $`r e f = [F':F]`$ | `Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg` | [Thm 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg.lean#L10) |
| multiplicativity in towers | `ramificationIndex_eq_mul_ramificationIndex_restrict`, `inertiaDeg_eq_mul_inertiaDeg_restrict`, `Place.ramificationIndexAlong_comp`, `inertiaDegAlong_comp` | [Sol 68–89](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L68-L89), [Thm 6](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp.lean#L6), [Thm 6](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_inertiaDegAlong_comp.lean#L6) |

## 7. Links

FLT sources at the pinned sha `aa2d8b3`:

- [Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean) — `Place`, `ord`, `ofHeightOneSpectrum`, the divisor types
- [Definitions/Def_AlgebraicCurve_DivisorPushPull.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean) — `restrict`, `ramificationIndex`, `inertiaDeg`, pushforward/pullback, the identity classes
- [Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean) — `integralClosureAt`, `center`, `fiberCenter`, `placeOfPrime`, `fiberEquiv`, `fiberOver`
- [Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean) — `SemilinearAut` and its actions
- [Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean) — the public valuation/order dictionary used for $`K(t)`$ in [017](017-rational-function-field-and-principal-divisors.md)
- [Definitions/Def_AlgebraicCurve_PlaceCompletion.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlaceCompletion.lean) — the completion API behind the local picture of §2
- [`P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean) — the residue/ramification dictionary and the fundamental identity
- [`P2M/Sol/S_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean) — Galois transitivity on the fibre
- [`P2M/Sol/S_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg.lean) — Galois constancy
- [`P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean) — tower multiplicativity and the exchange reduction

Mathlib at tag `v4.33.0`:

- [RingTheory/Valuation/ValuationSubring.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Valuation/ValuationSubring.lean) — `ValuationSubring`, its maximal ideal and residue field
- [RingTheory/DedekindDomain/AdicValuation.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean) — `HeightOneSpectrum` and its valuation
- [RingTheory/DedekindDomain/IntegralClosure.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean) — primes over a prime, `primesOverFinset`
- [NumberTheory/RamificationInertia/Ramification.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/RamificationInertia/Ramification.lean) — `Ideal.ramificationIdx'` and its specification
- [NumberTheory/RamificationInertia/Inertia.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/RamificationInertia/Inertia.lean) — `Ideal.inertiaDeg'`
- [NumberTheory/RamificationInertia/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/RamificationInertia/Basic.lean) — `Ideal.sum_ramification_inertia`, the fibre-sum identity used here (its modern form is `sum_ramification_inertia_eq_finrank` in `RingTheory/RamificationInertia/Basic.lean`)
- [NumberTheory/RamificationInertia/Galois.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/RamificationInertia/Galois.lean) — the Galois action on primes over a prime, `Ideal.exists_smul_eq_of_isGaloisGroup`

Companion notes:

- [008 — Divisors, linear equivalence, and Pic⁰](008-divisors-and-pic0.md) — §1–3 the dictionary for one field, §5 the divisor calculus this note makes available
- [001 — Field extensions and Galois basics](001-field-extensions-and-galois-basics.md) §4 — decomposition and inertia as subgroups
- [016 — Correspondences and the exchange lemma](016-correspondences-and-exchange.md) — the consumer of §3–§5
- [017 — The rational function field and principal divisors](017-rational-function-field-and-principal-divisors.md) — where the places of $`K(t)`$ are written down explicitly

Background:

- J.-P. Serre, *Local Fields*, GTM 67, Springer 1979, Ch. I — places, extensions, ramification and inertia, the fundamental identity.
- J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer 1999, Ch. I–II — the integral closure and the prime-splitting dictionary.
- R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer 1977, Ch. II §6, IV §2 — the geometric reading: points, fibres, and ramification of a cover of curves.
