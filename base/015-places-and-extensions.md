# Places and their extensions

**Status: OUTLINE — the mathematical scope and section plan, for review before the
prose is written.**

On a smooth projective curve over $`K`$, the points are the **places** of its
function field $`F/K`$: the discrete valuation rings $`\mathcal{O} \subset F`$ with
fraction field $`F`$ and containing $`K`$. The order of vanishing
$`\mathrm{ord}_P`$ and the residue field $`\kappa(P)`$ are read off from
$`\mathcal{O}`$, and the degree $`\deg P = [\kappa(P) : K]`$ weights divisors. Note
[008](008-divisors-and-pic0.md) develops that dictionary for a single field.

This note develops what happens when the field is **extended**. A place of $`F`$
generally does not remain a place of a finite extension $`F'/F`$; it splits into
finitely many places of $`F'`$, and two numbers govern the splitting. The
**ramification index** $`e`$ records how the uniformizer pulls apart, the
**inertia degree** $`f`$ records how the residue field grows, and their product
sums to the extension degree — the *fundamental identity*. When $`F'/F`$ is
Galois, the places over a given one form a single orbit and $`e`$ and $`f`$ are
constant on it; in general one passes to the separable closure and keeps a
*semilinear* action, because the automorphisms move the base field. Both numbers
are multiplicative in towers.

This is the local theory every pushforward or pullback computation rests on, and
it is the input to the exchange lemma of
[016](016-correspondences-and-exchange.md). It assumes 008 (the divisor
dictionary) and 001 §4 (decomposition and inertia as subgroups).

## 1. Places, valuation rings, and the order function

- A place is a discrete valuation ring $`\mathcal{O} \subset F`$ with fraction
  field $`F`$, containing $`K`$ and not equal to $`F`$; equivalently a
  $`K`$-trivial discrete valuation of $`F`$ up to equivalence. The maximal ideal
  $`\mathfrak{m}`$, a uniformizer $`\pi`$, the residue field
  $`\kappa = \mathcal{O}/\mathfrak{m}`$, and the degree $`[\kappa : K]`$.
- The normalized order $`\mathrm{ord}_P`$: every nonzero $`f`$ is
  $`u\pi^n`$, and $`\mathrm{ord}_P(f) = n`$. Its laws (additive, $`\mathrm{ord}(1)=0`$,
  $`\mathrm{ord}(f^{-1}) = -\mathrm{ord}(f)`$) and the finiteness of
  $`\{P : \mathrm{ord}_P(f) \neq 0\}`$.
- The order is a normalized $`\mathbb{Z}`$-valued valuation, and the other way
  round: the sign convention is a choice, and the valuation is recovered from its
  ring by $`\mathrm{ord}_P = -\log`$ of the associated adic valuation. The
  **uniqueness statement** — a $`\mathbb{Z}`$-valued valuation function whose
  nonnegative locus is exactly the ring is $`\mathrm{ord}_P`$ — is what makes the
  later dictionary computations legitimate.
- The three faces of the same data: a place, its valuation ring, its
  height-one prime in the relevant Dedekind domain, and its normalized valuation;
  the equivalences between them.

## 2. Extending a place to a finite extension

- Let $`F'/F`$ be finite and $`\mathcal{O}`$ a place of $`F`$. The **integral
  closure** $`\mathcal{O}'`$ of $`\mathcal{O}`$ in $`F'`$: a Dedekind domain,
  finite as an $`\mathcal{O}`$-module, with fraction field $`F'`$, and — since
  $`\mathcal{O}`$ is a DVR — a principal ideal domain.
- The places of $`F'`$ above the place $`v`$ of $`F`$ correspond to the nonzero
  prime ideals of $`\mathcal{O}'`$, i.e. to the points of the fibre; **the fibre
  is finite**. This is the algebraic form of "a point has finitely many
  preimages".
- The **centre** of a place $`w`$ of $`F'`$ on a subring, and the fact that the
  place over $`v`$ is determined by the corresponding maximal ideal
  $`\mathfrak{P} \subset \mathcal{O}'`$; the residue field of $`w`$ is
  $`\mathcal{O}'/\mathfrak{P}`$.
- The local picture: completing at $`v`$ turns the fibre into
  $`\prod_{w \mid v} F'_w`$ over the local field $`F_v`$, one factor per place
  above $`v`$ — the reason the fibre is finite and the local degrees add up.
- Why the integral closure is the right object rather than the field alone: it is
  the coordinate ring of the cover over the local ring of the point, so the fibre
  is literally its closed fibre.

## 3. Ramification, inertia, and the fundamental identity

- **Ramification index**: $`e(w/v) = \mathrm{ord}_w(\pi)`$, the exponent with
  $`\mathfrak{P}^{e}`$ exactly dividing $`\pi\mathcal{O}'`$; equivalently the
  ramification index of the local extension $`F'_w/F_v`$.
- **Inertia degree**: $`f(w/v) = [\kappa(w) : \kappa(v)]`$, the residue degree.
- The residue field as a quotient of the integral closure, and the two numbers as
  the ramification index and inertia degree of the corresponding extension of
  local rings; the local degree is $`e f`$.
- **The fundamental identity**
  $$[F' : F] \;=\; \sum_{w \mid v} e(w/v)\, f(w/v),$$
  and its meaning: the fibre weights $`e f`$ sum to the global degree. Consequence
  for divisors: pullback multiplies degree by $`[F':F]`$, pushforward preserves it,
  and both respect principal divisors.
- Finiteness of the fibre as a corollary, and the special case of an unramified
  place ($`e = 1`$, so $`f = [F':F]`$ when the fibre is a single point).

## 4. Galois and semilinear equivariance

- Suppose $`F'/F`$ is Galois with group $`G`$. Then $`G`$ acts on the places of
  $`F'`$ preserving orders and degrees, and it acts **transitively** on the places
  above a fixed $`v`$: the fibre is one orbit. Hence $`e`$ and $`f`$ are constant
  on the fibre, and $`|\text{fibre}| \cdot e \cdot f = [F':F]`$.
- The **decomposition group** of $`w`$ (its stabilizer) and its **inertia
  subgroup** (those acting trivially on the residue field); $`e = |I|`$ and
  $`f = |D/I|`$. This is where 001 §4's abstract subgroups acquire their
  arithmetic meaning.
- For a non-normal $`F'/F`$ there is no Galois group to act, but the
  automorphisms of the Galois closure that **move the base** still act, and the
  equivariance statements survive as *semilinear* ones: an automorphism sends a
  place to a place while twisting the constants, and $`\mathrm{ord}`$,
  $`\mathrm{deg}`$, $`e`$, $`f`$ are preserved. The transitivity statement becomes
  "the places above a common place are in one orbit" for the group over the
  base's Galois closure.
- **Multiplicativity in towers**: for $`F \subseteq E \subseteq F'`$,
  $$e(w/v) = e(w/w')\, e(w'/v), \qquad f(w/v) = f(w/w')\, f(w'/v)$$
  where $`w' = w|_E`$. These are the identities that let local computations at
  different levels be compared, and they are used in the bifibre count of 016.

## 5. The fibre over a place, intrinsically

- The fibre $`\{w : w \mid v\}`$ as a finite set, and the two competing
  descriptions: places of $`F'`$ restricting to $`v`$, versus maximal ideals of
  the integral closure above the maximal ideal of $`\mathcal{O}`$. The bijection
  between them, and its compatibility with orders and residue fields, is the
  technical core that the rest of the theory is stated through.
- The class-free nature of the fibre-over description: it needs no hypothesis
  beyond finiteness and integrality, unlike the divisor-level `fiber` of 008 §5
  which is tied to principal divisors. (This is why the exchange argument can use
  the fibre before knowing the residue theorem.)

## 6. How the code says all this

- A place is a `Place K F`, a `ValuationSubring` plus three fields; the residue
  field, degree, height-one spectrum, adic valuation and normalized `ord` are
  derived from it. The normalized order is `-log` of the adic valuation, and the
  uniqueness/dictionary lemmas are stated against mathlib's `Valuation` and
  `HeightOneSpectrum`.
- The extension is built on `integralClosureAt F' v`, with its Dedekind, fraction
  ring and finiteness instances; the fibre-centre prime and the bijection to the
  places above $`v`$ are `fiberCenter`/`placeOfPrime`/`fiberEquiv`, and the fibre
  set is `fiberOver`.
- The identification of FLT's `ramificationIndex`/`inertiaDeg` with mathlib's
  `Ideal.ramificationIdx'`/`Ideal.inertiaDeg'` of the fibre-centre prime, via the
  residue isomorphism
  $`\mathcal{O}'/\mathfrak{P} \cong \kappa(w)`$; the fundamental identity is an
  application of mathlib's `Ideal.sum_ramification_inertia_eq_finrank`.
- The Galois action is `SemilinearAut K F` (automorphisms that move the base),
  with the orbit and equivariance lemmas; the `K`-linear action of 008 §8 is the
  special case of automorphisms fixing `K`.

### Key point → declaration map

| Mathematics | Lean declaration |
|---|---|
| place as a valuation subring | `Place`, `Place.ext`, `toValuationSubring_injective` |
| discrete valuation ring instances | `Place.instIsDiscreteValuationRing`, `Place.instIsPrincipalIdealRing` |
| residue field, degree | `Place.ResidueField`, `Place.deg` |
| height-one prime, adic valuation, order | `Place.heightOneSpectrum`, `Place.adicValuation`, `Place.ord` |
| order laws | `Place.ord_mul`, `ord_inv`, `ord_zpow`, `ord_coe_unit`, `exists_unit_mul_zpow` |
| order vs valuation | `ord_eq_neg_log_of_valuationSubring_eq`, `isEquiv_adicValuation_of_valuationSubring_eq` |
| order-membership dictionary | `Place.mem_iff_ord_nonneg`, `mem_of_ord_nonneg`, `ord_nonneg_of_mem` |
| order of constants | `Place.ord_algebraMap` |
| place from a height-one prime | `Place.ofHeightOneSpectrum` |
| restriction of a place | `Place.restrict`, `ord_restrict`, `mem_restrict_iff` |
| integral closure at a place | `integralClosureAt`, its Dedekind/fraction-ring/finite instances |
| centre of a place | `Place.center`, `mem_center_iff_ord_pos`, `center_ne_bot` |
| fibre-centre prime | `Place.fiberCenter`, `mem_fiberCenter_iff_ord_pos`, `fiberCenter_liesOver` |
| places above $`v`$ ↔ primes of the integral closure | `Place.placeOfPrime`, `fiberEquiv`, `fiberOver`, `mem_fiberOver` |
| residue dictionary | `residueFieldEquivQuotientCenter`, `inertiaDeg_eq_inertiaDeg_fiberCenter` |
| ramification dictionary | `le_ord_iff_mem_pow_fiberCenter`, `ramificationIndex_eq_ramificationIdx_fiberCenter` |
| fundamental identity | `sum_ramificationIndex_mul_inertiaDeg_fiberOver`, `Ideal.sum_ramification_inertia_eq_finrank` |
| Galois constancy | `card_fiberOver_mul_ramificationIndex_mul_inertiaDeg` |
| semilinear automorphisms | `SemilinearAut`, `toRingAut`, `baseAut` |
| equivariance of order and degree | `Place.ord_smul`, `Place.deg_smul` |
| places above $`v`$ in one orbit | `Place.exists_algEquiv_smul_eq_of_restrict_eq` |
| equivariance of $`e`$ and $`f`$ | `ramificationIndex_eq_of_restrict_eq`, `inertiaDeg_eq_of_restrict_eq` |
| multiplicativity in towers | `ramificationIndex_eq_mul_ramificationIndex_restrict`, `inertiaDeg_eq_mul_inertiaDeg_restrict`, `Place.ramificationIndexAlong_comp`, `inertiaDegAlong_comp` |

## 7. Links

FLT sources at the pinned sha `aa2d8b3`:

- [Def_AlgebraicCurve_DivisorClassGroup.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean) — `Place`, `ord`, `ofHeightOneSpectrum`
- [Def_AlgebraicCurve_DivisorPushPull.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean) — `restrict`, `ramificationIndex`, `inertiaDeg`, `deg_restrict_mul_inertiaDeg`
- [Def_AlgebraicCurve_PlacesOverDVR.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean) — `integralClosureAt`, `center`, `fiberCenter`, `placeOfPrime`, `fiberEquiv`, `fiberOver`
- [Def_AlgebraicCurve_BaseChangeGalois.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean) — `SemilinearAut` and its action on places
- [`S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean) — the residue/ramification dictionary and the fibre-over identity

Mathlib at tag `v4.33.0`:

- [Valuation/ValuationSubring.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Valuation/ValuationSubring.lean) — `ValuationSubring`
- [DedekindDomain/AdicValuation.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean) — `HeightOneSpectrum` and its valuation
- [DedekindDomain/IntegralClosure.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean) — primes over a prime
- [NumberTheory/RamificationInertia/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/RamificationInertia/Basic.lean) — `Ideal.ramificationIdx'`, `Ideal.inertiaDeg'`
- [NumberTheory/RamificationInertia/Galois.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/RamificationInertia/Galois.lean) — the Galois action on primes over a prime

Companion notes:

- [008 — Divisors, linear equivalence, and Pic⁰](008-divisors-and-pic0.md) — the divisor dictionary, and §5's classical ramification
- [001 — Field extensions and Galois basics](001-field-extensions-and-galois-basics.md) §4 — decomposition and inertia as subgroups
- [016 — Correspondences and the exchange lemma](016-correspondences-and-exchange.md) — the exchange that consumes this note
