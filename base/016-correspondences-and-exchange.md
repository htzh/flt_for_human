# Correspondences and the exchange lemma

A **correspondence** between two curves is a multivalued map: the data of a
common cover and two maps out of it. On divisor classes it acts by pulling back
along one leg and pushing forward along the other, and the Hecke operators on
$`X_0(N)`$ are correspondences. What turns an indexed family of such operators
into a *ring* acting on the Jacobian is that they commute, and the commutativity
of two Hecke correspondences is the **exchange identity** for a fibre square.

[008 §5](008-divisors-and-pic0.md) introduces the pull–push calculus and the
shape $`T_\ell = \alpha_\ast \beta^\ast`$;
[math/009 §4](../math/009-hecke-jacobian-commute.md) states the divisor-level
identity that the commutativity proof turns on, and identifies the modular square
it is applied to. This note supplies the mathematics in between: the pull–push
action, the hypothesis that makes a square of function fields a fibre product,
the exchange identity, and the finite place-level count it reduces to. The count
is proved first in the Galois case by an orbit argument, then in general by
passing to the normal closure. The note closes with the **norm formula**, which
is what makes pushforward send principal divisors to principal divisors; that is
the last input [017](017-rational-function-field-and-principal-divisors.md) needs
to transfer the residue theorem to a general function field.

It assumes [015](015-places-and-extensions.md) (places, ramification, inertia,
semilinear equivariance, and their multiplicativity in towers) and
[008 §5](008-divisors-and-pic0.md) (the pull–push calculus). Line numbers pin
`anthropics/fermats-last-theorem@aa2d8b3`; mathlib citations point at tag
v4.33.0. The exchange has a definition layer in
[`Def_AlgebraicCurve_Correspondence.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean)
and a proof layer in three `P2M/Sol/` files; the `Theorems/` wrappers are
statement-for-statement re-exports.

## 1. Correspondences, and the pull–push action

**The two operations.** Fix a finite separable map of function fields
$`\varphi : F \to F'`$ over $`K`$. On points it has two behaviours: a point
$`v`$ of $`F`$ has finitely many preimages, and a point $`w`$ of $`F'`$ has one
image. The induced maps on divisors are the two weighted sums

$$\varphi^{\ast}\big([v]\big) \\;=\\; \sum_{w \mid v} e(w/v)\\,[w],
  \qquad
  \varphi_{\ast}\big([w]\big) \\;=\\; f(w/v)\\,\big[\varphi(w)\big],$$

extended by additivity. Pullback distributes a point over its fibre with the
ramification index as multiplicity; pushforward collapses a point onto its image
with the inertia degree as multiplicity. Both weights are exactly the ones
[015 §3](015-places-and-extensions.md) proves necessary for the degree to behave.
In the code they are the single-place formulas

```lean
-- Def_AlgebraicCurve_Correspondence.lean, lines 239 and 284
Divisor.pushforwardAlong_single : pushforwardAlong φ hφ (single w n)
  = single (w.restrictAlong φ hφ) (n * w.inertiaDegAlong φ hφ)
Divisor.pullbackAlong_single  : pullbackAlong u hu (single w₁ n)
  = ∑ W ∈ fiberAlong u hu w₁, single W (n * W.ramificationIndexAlong u)
```

([pushforward, line 239](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L239-L246);
[pullback, line 284](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L284-L292)).
The underlying `Divisor`-level definitions are
`Divisor.pushforward` ([DivisorPushPull, line 448](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L448-L456))
and `Divisor.pullback` ([line 549](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L549-L565)).

Note the asymmetry of hypotheses. Pushforward needs only that $`\varphi`$ is
integral — the fibre is not even needed, since each point is pushed individually.
Pullback needs the fibre to be finite, and the code obtains that from
`HasPrincipalDivisors K F'`
([`restrict_fiber_finite`, line 334](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L334-L342)).
This is the reason [015 §5](015-places-and-extensions.md) insists on the
class-free fibre `Place.fiberOver`: the local results must exist before the class
hypothesis does.

**Degree behaviour.** The weights are chosen so that

$$\deg \varphi^{\ast} D \\;=\\; [F':F] \cdot \deg D, \qquad
  \deg \varphi_{\ast} D' \\;=\\; \deg D'.$$

The first is the fundamental identity of
[015 §3](015-places-and-extensions.md); the second is
$`\deg w = \deg \varphi(w) \cdot f(w/\varphi(w))`$
(`degree_pushforward`, [`DivisorPushPull`, line 459](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L459-L467);
`degree_pullback`, [line 627](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L627-L632)
under `FundamentalIdentity`). Consequently both operations preserve the
degree-zero subgroup. Both also respect principal divisors — pullback because it
sends $`f`$ to $`\varphi(f)`$
([`isPrincipal_pullback`, line 598](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L598-L605)) —
so they descend to $`\mathrm{Pic}^0`$: `Pic0.pullbackHom`
([line 697](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L697-L705))
and `Pic0.pushforwardHom`
([line 721](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L721-L731)),
the latter conditional on the norm formula of §5. In the along-a-map vocabulary
the pullback and pushforward are `Divisor.pullbackAlong` and
`Divisor.pushforwardAlong`
([Correspondence, lines 67 and 99](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L67-L103)).

**What a correspondence is.** A correspondence between $`F`$ and itself (or
between two curves) is a pair of maps out of a common cover. In function-field
terms, two finite maps $`\varphi, \psi : F \to F'`$ give the endomorphism of
divisors

$$C_{\varphi,\psi} \\;=\\; \psi_{\ast} \circ \varphi^{\ast},$$

```lean
-- Def_AlgebraicCurve_Correspondence.lean, lines 137–138
def correspondence : Divisor K F →+ Divisor K F :=
  (pushforwardAlong ψ hψ).comp (pullbackAlong φ hφ)
```

([line 137](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L137-L138)).
Its degree is $`\deg \varphi \cdot \deg`$ (`degree_correspondence`,
[line 144](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L144-L146)),
and it descends to $`\mathrm{Pic}^0`$ (`Pic0.correspondence`,
[line 183](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L183-L187)).
The transposed correspondence is $`C_{\psi,\varphi} = \varphi_\ast \psi^\ast`$,
and *the question this note answers* is when the two agree:
$`C_{\varphi,\psi} = C_{\psi,\varphi}`$? For Hecke operators this is exactly
commutativity.

**The Hecke instance.** For the modular curve, $`T_\ell`$ is the correspondence
attached to the two degeneracy maps $`\alpha, \beta : X_0(N\ell) \to X_0(N)`$,
the forget-map and the $`q \mapsto q^\ell`$-map:
$`T_\ell = \alpha_\ast \beta^\ast`$. The abstract exchange lemma is instantiated
at the modular roof by `HeckeExchangeAt`
([`Def_ModularCurve_DegeneracyTower.lean`, line 121](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_DegeneracyTower.lean#L121-L132)),
which is literally the divisor exchange identity specialized to the tower maps,
and [math/009 §4](../math/009-hecke-jacobian-commute.md) is the full modular
account. Nothing in §§2–4 uses the modular curve; the note is pure function-field
algebra, and the Hecke case is one instantiation.

**Composition.** Correspondences compose: if $`C = \psi_\ast\varphi^\ast`$ acts
over one cover $`F_1`$ and $`C' = \psi'_\ast\varphi'^\ast`$ over another
$`F_2`$, and the two covers are tied together by maps $`u : F_1 \to Z`$ and
$`u' : F_2 \to Z`$ with a single exchange identity `hex` between the middle
pull–push pair, then $`C \circ C'`$ is again a correspondence:

```lean
-- Theorem …, line 6
Divisor.correspondence φ ψ hφ hψ (Divisor.correspondence φ' ψ' hφ' hψ' D)
  = Divisor.correspondence (u'.comp φ') (u.comp ψ) huφ' huψ D
```

(`Divisor.correspondence_correspondence`,
[Thm, line 6](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_correspondence_correspondence.lean#L6)).
The exchange identity is supplied as a hypothesis, not re-derived; this is the
algebraic form of "compose the two Hecke correspondences at the roof", and it is
why one exchange shape suffices for all pairs of primes: the roofs differ, the
shape does not.

## 2. The linearly disjoint square

**The square.** The exchange identity is a statement about a commuting square of
function fields

$$F \xrightarrow{\ a\ } A, \qquad F \xrightarrow{\ b\ } B, \qquad
  A \xrightarrow{\ a'\ } E, \qquad B \xrightarrow{\ b'\ } E,$$

with $`b' \circ b = a' \circ a`$, and every map finite, integral and separable.
Geometrically it is a square of curves; $`E`$ is the roof, $`A`$ and $`B`$ the
two sides, $`F`$ the base.

**The fibre-product condition.** The square is a fibre product over $`F`$ when
the roof is generated by the two images *and* the degrees multiply:

```lean
-- Def_AlgebraicCurve_Correspondence.lean / theorem hypotheses
(hgen : Algebra.adjoin K (Set.range a' ∪ Set.range b') = ⊤)
(hLD  : finrankAlong K (a'.comp a) = finrankAlong K a * finrankAlong K b)
```

(`hgen` and `hLD` are the literal code names of the two hypotheses in the
exchange theorem). Over an algebraically closed base, generation plus the degree
identity is precisely **linear disjointness** of the two extensions: the natural
map $`A \otimes_F B \to E`$ is an isomorphism. Geometrically the two covers meet
transversally over the base.

**The exchange (projection) identity.** For every divisor $`D`$ on $`A`$,

$$b^{\ast}\big(a_{\ast} D\big) \\;=\\;
  b'_{\ast}\big(a'^{\ast} D\big).$$

```lean
-- Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean, line 10
theorem … .pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
    (hsq : b'.comp b = a'.comp a) (hfin : FiniteAlong K (a'.comp a))
    (hsep : SeparableAlong K (a'.comp a)) (hgen : … = ⊤) (hLD : …) (D : Divisor K A) :
    Divisor.pullbackAlong b hb (Divisor.pushforwardAlong a ha D)
      = Divisor.pushforwardAlong b' hb' (Divisor.pullbackAlong a' ha' D)
```

([Thm, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean#L10)):
pull back along one side after pushing forward along the other gives the same
divisor whichever way round the square is traversed.

**Why the hypotheses are what they are.** Each hypothesis buys exactly one thing.

- *Finiteness and integrality* make pushforward defined and principal-preserving;
  the divisor-level statement also carries `[HasPrincipalDivisors K B]` and
  `[HasPrincipalDivisors K E]`, needed so that pullback's fibres exist (§1).
- *Separability* makes the tensor square étale: $`A \otimes_F B`$ is a product of
  fields rather than a local algebra, which is what makes the place count a
  finite sum and not a length. In the code it is the instance
  `Algebra.IsSeparable F E` on the composite; for characteristic-zero function
  fields it is automatic.
- *Generation* (`hgen`) makes the map from the tensor product to the roof
  surjective, so the roof is not a proper quotient of the fibre product.
- *The degree condition* (`hLD`) makes it injective — equivalently, makes the two
  legs' degrees exactly complementary, so no factor is lost.

The hypotheses are transported from the map-level formulation to an `Algebra`
structure by `algebraAlong` and its companions
([Correspondence, lines 14–53](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L14-L53)):
`FiniteAlong`, `SeparableAlong`, `FundamentalIdentityAlong` and
`NormFormulaAlong` are the side conditions, and `finrankAlong` is
$`[F':F]`$. This "along a map" vocabulary is what [015 §6](015-places-and-extensions.md)
records; here it is the language of the theorem statement.

## 3. Reduction to a single place

**Additivity.** Both sides of the exchange identity are additive in $`D`$ — they
are compositions of `AddMonoidHom`s — and `Divisor K A` is the free abelian
group $`\mathrm{Place} \to_0 \mathbb{Z}`$. So it suffices to check
$`D = [w_A]`$ with multiplicity one. The formal step is `Finsupp.addHom_ext`,
immediately after which the single-place formulas of §1 turn the goal into a
statement about one $`w_B`$.

**The coefficient.** Fix a place $`w_A`$ of $`A`$ and a place $`w_B`$ of $`B`$,
and let

$$T \\;=\\; \\{\\,W \in \mathrm{Place}(E) : W|_{A} = w_A,\ W|_{B} = w_B\\,\\}$$

be the **bifibre** — the places of the roof lying over both. The two sides of the
exchange identity have coefficients

$$\text{left} = \sum_{W \in T} e(W/w_B)\\, f(W/w_A),
  \qquad
  \text{right} = \sum_{W \in T} e(W/w_A)\\, f(W/w_B),$$

at $`[w_B]`$: pushing $`[w_A]`$ up to $`A`$-fibre points weights each $`W`$ by
its inertia over $`w_A`$, pulling down to $`B`$ weights by the ramification over
$`w_B`$, and the other order does the reverse. If $`w_A`$ and $`w_B`$ do *not*
lie over the same place of $`F`$, both sums are empty and both coefficients
vanish; that is the content of the `by_cases` split in the proof.

**What is left to prove.** The exchange identity is now the assertion that these
two sums agree, and that is where the local identity enters: it says that the
*same* bifibre sum, in a fixed ordering, has a value depending only on the two
base places. Writing $`F_1 = A`$, $`F_2 = B`$, $`v = w_A|_F = w_B|_F`$,

$$\sum_{W \in T} e(W/F_1)\\, f(W/F_2) \\;=\\;
  f(w_1/v)\\, e(w_2/v),$$

```lean
-- Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean, line 10
theorem … .sum_ramificationIndex_mul_inertiaDeg_exchange … :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂
      = w₁.inertiaDeg F * w₂.ramificationIndex F
```

([Thm, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L10)).
The right-hand side is symmetric in $`F_1, F_2`$ as a *product*, so swapping the
two legs turns the other ordering into the same number. Nothing about divisors
remains; the rest of the exchange proof is the cast from the $`\mathbb{N}`$-valued
local identity to the $`\mathbb{Z}`$-valued divisor identity, and the two
bookkeeping cases above.

## 4. The local identity: counting the bifibre

The technical core is the bifibre sum. The proof has a Galois case, where the
count is an orbit computation, and a general separable case, obtained by passing
to the normal closure. Both are worth seeing.

### 4.1 The Galois bifibre count

Assume $`E/F`$ is separable but not necessarily Galois, and let $`M/F`$ be a
finite Galois extension containing $`E`$ — the roof of roofs. The count that
drives everything is

$$\sum_{W \in T} e(W/F)\\, f(W/F) \\;=\\;
  \big(e(w_1/F)\\, f(w_1/F)\big)\big(e(w_2/F)\\, f(w_2/F)\big),$$

```lean
-- Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean, line 10
theorem … .sum_ramificationIndex_mul_inertiaDeg_bifiber (M : Type*) … [IsGalois F M] … :
    ∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F
      = (w₁.ramificationIndex F * w₁.inertiaDeg F) * (w₂.ramificationIndex F * w₂.inertiaDeg F)
```

([Thm, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean#L10)),
where the bifibre $`T`$ is now a set of places of the *small* roof $`E`$ and
$`M`$ is a Galois envelope in which the count is carried out. The proof
([Sol, lines 229–369](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean#L229-L369))
has three ingredients.

**Fiber-cardinality bookkeeping.** Choose $`P_1, P_2`$ in $`M`$ over
$`w_1, w_2`$ ([015 §2](015-places-and-extensions.md)'s
`Place.exists_restrict_eq`). The Galois constancy of
[015 §4](015-places-and-extensions.md),

$$|w.\mathrm{fiberOver}(M)| \cdot e(W/F)\\, f(W/F) \\;=\\; [M:F],$$

holds for every place $`W`$ of a Galois extension over a place $`w`$ of the base.
Applying it to $`v`$ over $`P_1`$, and to $`w_1`$ and $`w_2`$ over $`P_1`$,
$`P_2`$, and comparing with the tower multiplicativity of $`e`$ and $`f`$, turns
every local factor into the same $`P_1`$-quantity. The union of the fibres of the
places of $`T`$ inside $`M`$ is exactly
$`w_1.\mathrm{fiberOver}(M) \cap w_2.\mathrm{fiberOver}(M)`$ and the fibres are
disjoint, so the sum over $`T`$ is a cardinality times a common factor.

**The orbit/group layer.** This is the step that uses $`hgen`$ and $`hLD`$ as
group-theoretic hypotheses. Let $`G = \mathrm{Gal}(M/F)`$ and let

$$H_i \\;=\\; \mathrm{res}_{M/F_i}\big(\mathrm{Gal}(M/F_i)\big) \le G$$

be the image of the Galois group of $`M`$ over $`F_i`$ ($`i = 1,2`$). The index
is the relative degree, $`[G : H_i] = [F : F_i]`$
(`index_range_resHom`,
[Sol, line 136](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean#L136-L143)).
From `hgen` one gets $`H_1 \cap H_2 \le H_E`$: an automorphism fixing both
$`F_1`$ and $`F_2`$ fixes everything they generate, i.e. $`E`$
(`forall_apply_algebraMap_eq_of_adjoin_eq_top`,
[line 185](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean#L185-L203)).
From `hLD` one gets the index identity

$$[G : H_1 \cap H_2] \\;=\\; [G:H_1]\\,[G:H_2],$$

using the general inequality $`[G:H_1\cap H_2] \le [G:H_1][G:H_2]`$ together
with divisibility from the inclusion; and then

```lean
-- Thm_Subgroup_exists_eq_mul_of_index_inf_eq.lean, line 5
theorem Subgroup.exists_eq_mul_of_index_inf_eq (H₁ H₂ : Subgroup G)
    (h : (H₁ ⊓ H₂).index = H₁.index * H₂.index) (g : G) :
    ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂
```

([Thm, line 5](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_Subgroup_exists_eq_mul_of_index_inf_eq.lean#L5))
produces the product decomposition $`H_1 H_2 = G`$. This is the precise sense in
which `hgen` + `hLD` say "the two subgroups are independent": their product is
the whole group.

**The orbit-intersection identity.** For a finite group acting transitively on a
set $`X`$ and subgroups with $`H_1H_2 = G`$, the intersection of two orbits has
size the product of the orbit sizes divided by $`|X|`$:

```lean
-- Thm_MulAction_ncard_orbit_inter_orbit_mul_card.lean, line 5
theorem MulAction.ncard_orbit_inter_orbit_mul_card … (hprod : ∀ g, ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁*h₂)
    (x₁ x₂ : X) :
    (orbit H₁ x₁ ∩ orbit H₂ x₂).ncard * Nat.card X = (orbit H₁ x₁).ncard * (orbit H₂ x₂).ncard
```

([Thm, line 5](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_MulAction_ncard_orbit_inter_orbit_mul_card.lean#L5)).
This is a project theorem, not a mathlib one. It is applied to the transitive
$`G`$-set $`X = G \cdot P_1`$, the orbit of a place over $`v`$. The two orbit
identities

$$G \cdot P \\;=\\; (P|_F).\mathrm{fiberOver}(M), \qquad
  H_i \cdot P \\;=\\; (P|_{F_i}).\mathrm{fiberOver}(M)$$

(`orbit_gal_eq`,
[Sol, line 160](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean#L160-L168);
`orbit_range_resHom_eq`,
[line 147](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean#L147-L156))
convert ncard of orbits into the fibre cardinalities already related to local
degrees, and the last degree identity

$$[F_1:M]\\,[F_2:M] \\;=\\; [F:M]\\,[E:M]$$

follows from `hLD` and `Module.finrank_mul_finrank`. Cancelling the common
factor $`[F:M][E:M]`$ gives the count.

### 4.2 From the Galois count to the exchange

The Galois count is in the "same field on both sides" form
$`\sum e(W/F)f(W/F)`$; the exchange needs the crossed form
$`\sum e(W/F_1) f(W/F_2)`$ and a right side with no local factors. The passage is
the **tower multiplicativity** of [015 §4](015-places-and-extensions.md):

$$e_F(W) = e_{F_1}(W)\\, e_F(w_1), \qquad
  f_F(W) = f_{F_2}(W)\\, f_F(w_2)$$

(`Place.ramificationIndex_eq_mul_ramificationIndex_restrict`,
[Sol, line 68](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L68-L77);
`inertiaDeg_eq_mul_inertiaDeg_restrict`,
[line 81](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L81-L89)).
Substituting into the Galois count, the factor
$`e_F(w_1) f_F(w_2)`$ is common to every term and cancels against the same
product on the right; positivity of the cancelled factor
($`e_F(w_1) \gt 0`$ and $`f_F(w_2) \gt 0`$) is what licenses the cancellation, and
it is established from `Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg`
and `Module.finrank_pos`. This is `exchange_of_isGalois`
([Sol, lines 148–195](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L148-L195)).
This cancellation is the *only* place tower multiplicativity is used, and it is
why the local identity is a statement about one bifibre rather than about two
nested extensions.

### 4.3 The general separable case

If $`E/F`$ is separable but not Galois, there is no group to act on $`E`$, so the
count is performed in a Galois envelope. The code takes

$$E^{\mathrm{env}} \\;=\\; \text{the normal closure of } E \text{ over } F
  \text{ inside } \overline{E},$$

```lean
-- P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean, lines 99–108
abbrev Env : Type _ := ↥(IntermediateField.normalClosure F E (AlgebraicClosure E))
theorem isGalois_env [FiniteDimensional F E] [Algebra.IsSeparable F E] : IsGalois F (Env F E)
```

([Sol, lines 99–108](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L99-L108)).
`isGalois_env` proves normality from the ambient algebraic closure and
separability from `IntermediateField.isSeparable_iSup`. The envelope is made an
$`F_i`$-algebra by `algebraEnv`, with four scalar-tower instances covering every
level of the tower $`K \subseteq F \subseteq F_i \subseteq E \subseteq E^{\mathrm{env}}`$
([lines 110–144](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L110-L144)).
The Galois count is then applied to $`E^{\mathrm{env}}`$; the places of $`E`$ over
a given place are exactly the restrictions of the places of $`E^{\mathrm{env}}`$,
and $`e`$ and $`f`$ are multiplicative in the tower, so the count transports back
down. This is
`sum_ramificationIndex_mul_inertiaDeg_bifiber_of_isSeparable` and the final
`solution`
([Sol, lines 201–255](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L201-L255)).
The whole `Env`/`isGalois_env` layer is private to the solution file; there is no
`Theorems/` wrapper, which is why the note cites the `P2M/Sol/` path for this
step.

### 4.4 The degenerate case

If the two legs of the correspondence are the same map, $`C`$ commutes with
itself and no exchange is needed. Correspondingly, the Hecke commutativity
theorem treats $`\ell = \ell'`$ separately
([math/009 §4](../math/009-hecke-jacobian-commute.md)). The proof of the general
statement only ever runs for two *distinct* legs, and the code's main exchange
requires the two `AlgHom`s to be genuinely different in that case.

## 5. Pushforward of principal divisors, and the norm formula

**The norm.** A finite map pushes a principal divisor to a principal divisor
because it sends a function to its norm: the function whose divisor is the
pushforward is

$$N_{F'/F}(f), \qquad
  \varphi_{\ast}\\,\mathrm{div}(f) \\;=\\; \mathrm{div}\big(N_{F'/F} f\big).$$

The local form is the **norm formula**: at each place $`v`$ of the base,

$$v.\mathrm{ord}\big(N_{F'/F} f\big) \\;=\\;
  \sum_{w \mid v} f(w/v)\\, w.\mathrm{ord}(f),$$

```lean
-- Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver.lean, line 9
theorem … .ord_norm_eq_sum_fiberOver … [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    [CharZero F] (v : Place K F) (hf : f ≠ 0) :
    v.ord (Algebra.norm F f) = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f
```

([Thm, line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver.lean#L9)).
Note that the weight is the *inertia degree*, not $`e f`$: the norm formula is
the local form of "pushforward is inertia-weighted", and the ramification index
has already been absorbed into the order of $`f`$ at the places above. The three
hypotheses are finite-dimensionality, separability, and — in this version — a
`[CharZero F]` instance, which is an artefact of the `Ideal.relNorm` route
through which the project first proves the formula. The twin
`ord_norm_eq_sum_fiberOver_of_isSeparable`
([Thm, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver_of_isSeparable.lean#L10))
drops `[CharZero F]`; the naming is a historical accident, and the
`_of_isSeparable` statement is the stronger one.

**How the formula is proved.** It is a computation with the relative norm of an
ideal, prime by prime over the fibre-centre primes of
[015 §2–§3](015-places-and-extensions.md):

- the relative norm of the fibre-centre prime is the base maximal ideal to the
  inertia degree,
  $`\mathrm{relNorm}(\mathfrak{P}) = \mathfrak{m}_v^{\,f}`$
  (`relNorm_fiberCenter`,
  [Sol, line 445](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver.lean#L445));
- the multiplicity of $`\mathfrak{m}_v`$ in the principal ideal generated by an
  integral element is its order
  (`count_normalizedFactors_span_singleton`,
  [Thm, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_count_normalizedFactors_span_singleton.lean#L10));
- assembling the factorizations gives the norm of a principal ideal as a power of
  $`\mathfrak{m}_v`$ with exponent the weighted sum of orders
  (`relNorm_span_singleton`,
  [Sol, line 475](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver.lean#L475));
- clearing denominators for a general $`f = a/b`$ gives the stated identity.

**The predicate, not a class.** The norm formula is packaged as a `Prop`, not a
type class:

```lean
-- Def_AlgebraicCurve_DivisorPushPull.lean, lines 483–485
def PushforwardNormFormula [Module.Finite F F'] : Prop :=
  ∀ (f : F'), f ≠ 0 → ∀ D : Divisor K F', (∀ w, D w = w.ord f) →
    ∀ v : Place K F, pushforward F D v = v.ord (Algebra.norm F f)
```

([line 483](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L483-L485)).
From it, principal divisors are preserved by pushforward:

```lean
-- lines 494–498
theorem isPrincipal_pushforward_of_normFormula (H : PushforwardNormFormula K F F')
    {D : Divisor K F'} (hD : IsPrincipal D) : IsPrincipal (pushforward F D)
```

([line 494](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L494-L498)):
the witnessing function is $`\mathrm{Algebra.norm}\, f`$, and `Algebra.norm` is
nonzero on nonzero elements. The project supplies the formula in both the
`CharZero` and the `_of_isSeparable` forms
(`Divisor.pushforwardNormFormula`,
[Thm, line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_pushforwardNormFormula.lean#L9)),
and `NormFormulaAlong` is the map-level spelling
([Correspondence, line 43](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L43-L47)).
This is the second input — besides degree preservation — that lets a
correspondence descend to $`\mathrm{Pic}^0`$.

**What 017 does with it.** Since pushforward preserves degree and sends
$`\mathrm{div}(f)`$ to $`\mathrm{div}(N f)`$,

$$\deg \mathrm{div}(f) \\;=\\; \deg \mathrm{div}\big(N_{F/K(t)} f\big),$$

so the residue theorem for $`F`$ follows from the residue theorem for the
rational function field $`K(t)`$. That transfer is
[017 §4](017-rational-function-field-and-principal-divisors.md), and it is the
reason the norm formula is proved here rather than there.

**A companion result with a defect.** The project also proves a corrected bifibre
identity for the case where the degree condition `hLD` *fails*, adding one extra
term when the two places have the same restriction to $`F_2`$
(`sum_ramificationIndex_mul_inertiaDeg_bifiber_defect`,
[Thm, line 11](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber_defect.lean#L11)).
That "defect" theorem is not on the path of the main exchange — it serves a
different, non-linearly-disjoint degeneration in the Hecke-diagonal argument —
and no result in this note or in [017](017-rational-function-field-and-principal-divisors.md)
depends on it.

## 6. How the code says all this

The development splits cleanly into a definition layer and a proof layer.

**Definition layer.**
[`Def_AlgebraicCurve_Correspondence.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean)
holds the "along a map" vocabulary (`algebraAlong`, `FiniteAlong`,
`SeparableAlong`, `FundamentalIdentityAlong`, `NormFormulaAlong`, `finrankAlong`),
the map-level pullback/pushforward (`Divisor.pullbackAlong`,
`Divisor.pushforwardAlong`, the two `_single` formulas), the correspondence on
divisors and on `Pic0` (`Divisor.correspondence`, `Pic0.correspondence`), and the
`IntertwinesAlong` relation used by [015 §4](015-places-and-extensions.md).
[`Def_AlgebraicCurve_DivisorPushPull.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean)
holds the underlying `Divisor.pushforward`/`Divisor.pullback`,
`PushforwardNormFormula`, the two identity classes `FundamentalIdentity` and
`SumRamificationInertia`, and the descent to `Pic0`.

**Proof layer.** Each numerical theorem is proved in a `P2M/Sol/S_*.lean` file and
re-exported by a short `Theorems/Thm_*.lean` wrapper:

- the exchange itself:
  [`S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean)
  (the `Finsupp` reduction);
- the local identity and the normal-closure reduction:
  [`S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean);
- the Galois count:
  [`S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean);
- the norm formula:
  [`S_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver.lean).

Three points about the encoding are easy to trip over.

1. **The exchange reduces by `Finsupp.addHom_ext`, not by a divisor induction.**
   Because `Divisor` *is* a finitely supported function, additivity of both sides
   is definitional and the reduction to a single place is one line. This is the
   payoff of the `Finsupp` design of [008 §8](008-divisors-and-pic0.md), and it
   is also what makes the class-free `fiberOver` necessary: pullback needs fibre
   finiteness, which is available from `HasPrincipalDivisors` only after the norm
   formula is proved, so the local identity is proved from `fiberOver` first and
   transferred to `fiber` afterwards.
2. **The local identity is $`\mathbb{N}`$-valued, the divisor identity
   $`\mathbb{Z}`$-valued.** The code carries out the crossing and then casts with
   `exact_mod_cast`; a reader comparing statements should not be surprised by the
   `ℕ` versus `ℤ` difference.
3. **`PushforwardNormFormula` is a `Prop`-valued `def`, not a class.** Only
   `FundamentalIdentity` and `SumRamificationInertia` are classes. This matters
   because the norm formula is passed around as an explicit hypothesis — it is
   *not* synthesizable — and the wrappers `NormFormulaAlong` exist to keep that
   hypothesis legible.

### Key point → declaration map

| Mathematics | Lean declaration | Location |
|---|---|---|
| a map as an algebra structure | `algebraAlong`, `isScalarTower_along`, `isIntegral_along` | [Correspondence 14–24](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L14-L24) |
| bundled finiteness, separability, degree, identity, norm formula | `FiniteAlong`, `SeparableAlong`, `finrankAlong`, `FundamentalIdentityAlong`, `NormFormulaAlong` | [37–53](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L28-L53), [308](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L308-L310) |
| pullback and pushforward along a map | `Divisor.pullbackAlong`, `Divisor.pushforwardAlong` | [67](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L67-L92), [99](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L99-L126) |
| the single-place formulas | `Divisor.pushforwardAlong_single`, `Divisor.pullbackAlong_single` | [239](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L239-L246), [284](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L284-L292) |
| degree of pullback and pushforward | `degree_pullbackAlong`, `degree_pushforwardAlong` | [80](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L80-L86), [106](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L106-L111) |
| fibre along a map | `Place.fiberAlong`, `Place.mem_fiberAlong` | [269–282](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L269-L282) |
| the correspondence on divisors and on $`\mathrm{Pic}^0`$ | `Divisor.correspondence`, `Pic0.correspondence` | [137](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L137-L157), [183](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L183-L192) |
| composition of correspondences | `Divisor.correspondence_correspondence` | [Thm 6](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_correspondence_correspondence.lean#L6) |
| commutativity from one exchange | `Divisor.correspondence_comm_of_exchange`, `Pic0.correspondence_correspondence_comm` | [Thm 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_correspondence_comm_of_exchange.lean#L8), [Thm 6](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Pic0_correspondence_correspondence_comm.lean#L6) |
| the linearly disjoint square | the `hgen`/`hLD` hypotheses | [Thm 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean#L10) |
| the exchange identity | `Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong` | [Thm 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean#L10) |
| reduction to one place | `Finsupp.addHom_ext` | [Sol 89](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean#L89-L95) |
| the local identity | `Place.sum_ramificationIndex_mul_inertiaDeg_exchange` | [Thm 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L10) |
| the bifibre count (Galois) | `Place.sum_ramificationIndex_mul_inertiaDeg_bifiber` | [Thm 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean#L10) |
| index product / $`H_1H_2 = G`$ | `Subgroup.exists_eq_mul_of_index_inf_eq` | [Thm 5](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_Subgroup_exists_eq_mul_of_index_inf_eq.lean#L5) |
| orbit-intersection count | `MulAction.ncard_orbit_inter_orbit_mul_card` | [Thm 5](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_MulAction_ncard_orbit_inter_orbit_mul_card.lean#L5) |
| orbits are fibres | `orbit_gal_eq`, `orbit_range_resHom_eq` | [Sol 147](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean#L147-L168) |
| normal closure and the general separable case | `Env`, `isGalois_env`, `exchange_of_isGalois`, `…_bifiber_of_isSeparable` | [Sol 99–108](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L99-L108), [148](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L148-L255) |
| norm pushes principal to principal | `PushforwardNormFormula`, `isPrincipal_pushforward_of_normFormula` | [DivisorPushPull 483](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L483-L498) |
| the norm formula | `Place.ord_norm_eq_sum_fiberOver` | [Thm 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver.lean#L9) |
| relative norm of the fibre-centre prime | `relNorm_fiberCenter`, `relNorm_span_singleton`, `count_normalizedFactors_span_singleton` | [Sol 445](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver.lean#L445), [475](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver.lean#L475), [Thm 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_count_normalizedFactors_span_singleton.lean#L10) |
| the Hecke instance of the square | `HeckeExchangeAt` | [DegeneracyTower 121](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_DegeneracyTower.lean#L121-L132) |

## 7. Links

FLT sources at the pinned sha `aa2d8b3`:

- [Definitions/Def_AlgebraicCurve_Correspondence.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean) — `algebraAlong`, the `…Along` predicates, `pullbackAlong`, `pushforwardAlong`, `correspondence`
- [Definitions/Def_AlgebraicCurve_DivisorPushPull.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean) — `pushforward`, `pullback`, `PushforwardNormFormula`, the identity classes
- [Definitions/Def_ModularCurve_DegeneracyTower.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_DegeneracyTower.lean) — the Hecke roof square and `HeckeExchangeAt`
- [`P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean) — the exchange proof
- [`P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean) — the local identity and the normal-closure reduction
- [`P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean) — the Galois count
- [`P2M/Sol/S_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver.lean) — the norm formula
- [`P2M/Sol/S_AlgebraicCurve_Divisor_correspondence_correspondence.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Divisor_correspondence_correspondence.lean) — composition of correspondences

Mathlib at tag `v4.33.0`:

- [FieldTheory/Normal/Closure.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Normal/Closure.lean) — `IntermediateField.normalClosure`
- [FieldTheory/SeparableClosure.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/SeparableClosure.lean) — separability of the closure, `IntermediateField.isSeparable_iSup`
- [GroupTheory/Index.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/GroupTheory/Index.lean) — subgroup indices, `index_inf_le`, `index_dvd_of_le`
- [Algebra/Group/Action/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Group/Action/Basic.lean) — orbits and orbit–stabiliser
- [FieldTheory/Galois/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean) — `IsGalois.card_aut_eq_finrank`
- [RingTheory/Ideal/Norm/RelNorm.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Ideal/Norm/RelNorm.lean) — `Ideal.relNorm`

Companion notes:

- [008 — Divisors, linear equivalence, and Pic⁰](008-divisors-and-pic0.md) §5 — the classical pull–push and correspondence
- [015 — Places and their extensions](015-places-and-extensions.md) — ramification, inertia, their multiplicativity, and the class-free fibre
- [017 — The rational function field and principal divisors](017-rational-function-field-and-principal-divisors.md) — where the norm formula is used
- [math/009 — The Hecke action on the Jacobian](../math/009-hecke-jacobian-commute.md) §3–§4 — the Hecke instance of the square and the commutativity theorem

Background:

- W. Fulton, *Intersection Theory*, 2nd ed., Springer 1998, Ch. 1–2 — proper pushforward, flat pullback, and the projection formula.
- R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer 1977, Ch. II §6, III §9 — fibres of a morphism and base change.
- J.-P. Serre, *Local Fields*, GTM 67, Springer 1979, Ch. I §4, II §2 — the local degree and the norm.
- P. Deligne, *Formes modulaires et représentations $`\ell`$-adiques*, in *Séminaire Bourbaki 1968/69*, exposé 355 — correspondences on modular curves and the Eichler–Shimura relation.
