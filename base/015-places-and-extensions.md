# Places and their extensions: the fibre-centre dictionary

**Status: OUTLINE — for review. The prose is not yet written; this file fixes the
scope, the section plan and the declaration inventory so the coverage can be
checked first.** Planned as `base/015`, the first of the three notes that carry the
mathlib-level mathematics of the `AlgebraicCurve` port
([../lean/PORTING-AC.md](../lean/PORTING-AC.md), topics **T1–T3**).

## Why this note

[008](008-divisors-and-pic0.md) §1 and §8 introduce `Place`, `ord` and `deg`, and
§5 gives the classical ramification/inertia/fundamental-identity story. What 008
does **not** cover is what the port actually has to write:

1. the **interface** by which `Place.ord` is compared with mathlib's
   `Valuation`/`HeightOneSpectrum`/`adicValuation` — the port's highest-indegree
   surface (`Place.mem_iff_ord_nonneg` has 184 external citers);
2. the **extension of a place** to an integral extension `F'/F`, through the
   integral closure at the valuation ring, the fibre-centre prime, and the
   identification of FLT's `ramificationIndex`/`inertiaDeg` with mathlib's
   `Ideal.ramificationIdx'`/`Ideal.inertiaDeg'`;
3. the **Galois and semilinear equivariance** of all of that.

Note [001](001-field-extensions-and-galois-basics.md) §4 supplies the *abstract*
decomposition and inertia subgroups; this note supplies the place-level calculus
those abstractions are used through in the exchange argument. It is the local half
of [016](016-correspondences-and-exchange.md).

## Planned sections

### 0. Scope and placement
- What is a place, again (one paragraph, pointing at 008 §1 for the classical
  picture); the two actions this note needs — the `K`-linear `F ≃ₐ[K] F` action
  of 008 §4 and the **semilinear** action that moves `K`.
- Reading order: this note → [016](016-correspondences-and-exchange.md) →
  [017](017-rational-function-field-and-principal-divisors.md).

### 1. The `Place`↔mathlib bridge (T1)
- `Place` is a `ValuationSubring` with three fields; `Place.ext`,
  `toValuationSubring_injective`; the derived `IsDiscreteValuationRing`,
  `IsPrincipalIdealRing`, `Algebra K v.toValuationSubring`, `IsScalarTower`.
- `heightOneSpectrum`, `adicValuation := v.heightOneSpectrum.valuation F`, and
  `ord := -WithZero.log (v.adicValuation f)`: why `ord` is normalised the way it
  is, and why `ord` is not literally a mathlib `Valuation`.
- The interface lemmas and what each transports:
  `mem_iff_ord_nonneg`, `ord_nonneg_of_mem`, `mem_of_ord_nonneg`,
  `ord_algebraMap`, `ord_mul`, `ord_inv`, `ord_zpow`, `ord_coe_unit`,
  `ord_coe_irreducible`, `exists_unit_mul_zpow`.
- The valuation-subring dictionary:
  `ord_eq_neg_log_of_valuationSubring_eq`,
  `isEquiv_adicValuation_of_valuationSubring_eq`,
  `isEquiv_adicValuation_ofHeightOneSpectrum`,
  `adicValuation_valuationSubring`, `mem_iff_adicValuation_le_one`,
  `mem_maximalIdeal_iff_adicValuation_lt_one`,
  `adicValuation_isRankOneDiscrete`, `adicValuation_isTrivialOn`,
  `ord_ofHeightOneSpectrum_ne_zero_iff`.
- The converse construction `Place.ofHeightOneSpectrum` and its
  `toValuationSubring` computation — the bridge the ℙ¹ note (017) builds its
  places on.
- Two integration lemmas used by the principal-divisor route:
  `mem_toValuationSubring_of_isIntegral_adjoin`,
  `ord_eq_zero_of_isIntegral_adjoin`.

### 2. Extending a place to an integral extension (T2)
- The setup `F ⊆ F'` integral (later finite); `Place.restrict` and
  `restrict_toValuationSubring`, `mem_restrict_iff`, `ord_restrict`.
- `valuationSubringAlgebra` (a `@[reducible]` `Algebra v.toValuationSubring F'`)
  and `integralClosureAt F' v := integralClosure v.toValuationSubring F'`, with the
  `IsDedekindDomain`/`IsFractionRing`/finite/`IsTorsionFree` instances and
  `algebraMap_integralClosureAt_injective`. Why the reducibility is load-bearing.
- The centre of a place over a subring: `center`, `mem_center_iff`,
  `mem_center_iff_ord_pos`, `center_ne_bot`, `centerHeightOneSpectrum`,
  `toValuationSubring_eq_of_forall_mem`.
- The fibre-centre prime: `fiberCenter (hw : w.restrict F = v)`,
  `mem_fiberCenter_iff_ord_pos`, `fiberCenter_liesOver`,
  `toValuationSubring_eq_of_restrict_eq`, `forall_mem_of_restrict_eq`.
- `placeOfPrime`, `restrict_placeOfPrime`, `fiberCenter_placeOfPrime`,
  `eq_of_fiberCenter_eq`: the bijection between the places over `v` and the
  height-one primes of `integralClosureAt F' v`.
- `fiberEquiv`, `finite_setOf_restrict_eq`, `fiberOver`, `mem_fiberOver`,
  `restrict_mem_fiberOver`, `restrict_eq_of_mem_fiberOver`; and why the exchange
  uses `fiberOver` (class-free) rather than `fiber` (which needs
  `HasPrincipalDivisors`): `fiber_eq_fiberOver`.

### 3. The residue dictionary and the mathlib ramification identity (T2)
- The residue-field computation: `residueOfCenter`, `residueOfCenter_apply`,
  `ker_residueOfCenter`, `surjective_residueOfCenter`,
  `residueFieldEquivQuotientCenter` — the isomorphism
  `integralClosureAt ⧸ fiberCenter ≃+* w.ResidueField`, and
  `Algebra.finrank_eq_of_equiv_equiv` as the reason it computes `inertiaDeg`.
- `inertiaDeg_eq_inertiaDeg_fiberCenter`: FLT's `inertiaDeg` **is** mathlib's
  `Ideal.inertiaDeg'` of the fibre prime.
- `le_ord_iff_mem_pow_fiberCenter` and
  `ramificationIndex_eq_ramificationIdx_fiberCenter`: FLT's `ramificationIndex`
  **is** `Ideal.ramificationIdx'`.
- `neg_log_valuation_fiberCenter_eq_ord` and `eq_ord_of_addHom_of_nonneg_iff`:
  the uniqueness argument that identifies `-log ∘ fiberCenter.valuation` with
  `ord`, and why this lemma is the conceptual centre of the dictionary.
- mathlib on the other side: `primesOverFinset`,
  `IsDedekindDomain.mem_primesOverFinset_iff`, `Ideal.under`,
  `Ideal.ramificationIdx'`/`Ideal.inertiaDeg'`, `Ideal.sum_ramification_inertia_eq_finrank`.

### 4. The fibre-over degree formula (T2)
- `sum_ramificationIndex_mul_inertiaDeg_fiberOver`:
  $`\sum_{w \mid v} e(w)\,f(w) = [F' : F]`$ — statement, the `Finset.sum_bij`
  along `placeOfPrime`, and the appeal to
  `Ideal.sum_ramification_inertia_eq_finrank`.
- `subset_fiberOver_of_forall_restrict_eq` and the `le_finrank` corollary.
- `exists_restrict_eq`: every place of `F'` restricts to one of `F`.
- `card_fiberOver_mul_ramificationIndex_mul_inertiaDeg`: the Galois constancy
  lemma `|fiberOver| · e · f = [F' : F]` when `F'/F` is Galois — the single-prime
  input to the bifibre count of 016.

### 5. Galois and semilinear equivariance (T3)
- `SemilinearAut K F`: automorphisms of `F` that move the base through a
  `baseAut : K ≃+* K`, i.e. the Galois action without assuming `F/K` Galois;
  `toRingAut`, `baseAut`, `commutes`, `ofAlgAut`.
- The action on places: `SMul`/`MulAction` on `Place`, `smul_toValuationSubring`,
  `ord_smul` ($`\mathrm{ord}_{gv}(gf) = \mathrm{ord}_v(f)`$), `deg_smul`,
  `smulResidueRingEquiv`.
- `exists_algEquiv_smul_eq_of_restrict_eq`: the places over a common `v` form one
  orbit — the statement that replaces "decomposition group" from 001 §4 with a
  place-level equality. Uses mathlib's
  `Ideal.exists_smul_eq_of_isGaloisGroup`/`galRestrict`.
- `restrict_ofAlgAut_smul`, `ramificationIndex_eq_of_restrict_eq`,
  `inertiaDeg_eq_of_restrict_eq`, `ord_smul_of_ne_zero`.
- Tower multiplicativity: `ramificationIndex_eq_mul_ramificationIndex_restrict`,
  `inertiaDeg_eq_mul_inertiaDeg_restrict`, and the `Along` forms
  `ramificationIndexAlong_comp`, `inertiaDegAlong_comp`,
  `restrictAlong_restrictAlong`. This is the §5 identity of 008 in the shape the
  port needs.

### 6. How the code says this
- Encoding choices: `Place` as the valuation subring; the `'`-copies and the
  instance diamonds they work around; the `@[reducible]` `integralClosureAt`;
  `fiberOver` vs `fiber`.
- Key-point → declaration map (the table above, as a rendered table with pinned
  `#L` links).
- Traps: `Place`'s `isPrincipalIdealRing'` field; the `exp`/`log` `rfl`
  identifications; `DecidableEq (Place K F)`; the deprecated `Ideal` alias set
  (`sum_ramification_inertia`, `ramificationIndex_spec`, `inertiaDeg_algebraMap`).

### 7. Links
- FLT sources at `aa2d8b3`: `Def_AlgebraicCurve_DivisorClassGroup`,
  `Def_AlgebraicCurve_DivisorPushPull`, `Def_AlgebraicCurve_PlacesOverDVR`,
  `Def_AlgebraicCurve_BaseChangeGalois`, the `S_` files of T1–T3, and their
  `Theorems/` wrappers.
- mathlib at `v4.33.0`: `Valuation/ValuationSubring`, `DedekindDomain/AdicValuation`,
  `DedekindDomain/IntegralClosure`, `RamificationInertia/*`,
  `IntegralClosure/IntegrallyClosed`, `LocalRing/ResidueField`.
- Companion notes: [008](008-divisors-and-pic0.md) (the classical layer and the
  encoding of `Place`), [001](001-field-extensions-and-galois-basics.md) §4
  (decomposition/inertia as subgroups),
  [016](016-correspondences-and-exchange.md) (the exchange that consumes all of
  this), [math/009](../math/009-hecke-jacobian-commute.md) §4.

## Planned key-point → declaration map

| Mathematics | Lean declaration | AC topic |
|---|---|---|
| place as a valuation subring | `Place`, `Place.ext` | T1 |
| adic valuation and order of vanishing | `Place.adicValuation`, `Place.ord` | T1 |
| `ord` vs `valuation` | `ord_eq_neg_log_of_valuationSubring_eq`, `isEquiv_adicValuation_of_valuationSubring_eq` | T1 |
| `ord`-membership interface | `mem_iff_ord_nonneg`, `mem_of_ord_nonneg`, `ord_nonneg_of_mem` | T1 |
| `ord` of constants | `ord_algebraMap` | T1 |
| place from a height-one prime | `Place.ofHeightOneSpectrum` | T1 |
| restriction of a place | `Place.restrict`, `ord_restrict` | T2 |
| integral closure at a place | `integralClosureAt`, its instances | T2 |
| fibre-centre prime | `fiberCenter`, `mem_fiberCenter_iff_ord_pos`, `fiberCenter_liesOver` | T2 |
| places over `v` ↔ primes over the maximal ideal | `fiberEquiv`, `fiberOver`, `mem_fiberOver` | T2 |
| residue dictionary | `residueFieldEquivQuotientCenter`, `inertiaDeg_eq_inertiaDeg_fiberCenter` | T2 |
| ramification dictionary | `ramificationIndex_eq_ramificationIdx_fiberCenter` | T2 |
| the fibre-over identity | `sum_ramificationIndex_mul_inertiaDeg_fiberOver` | T2 |
| Galois constancy at one prime | `card_fiberOver_mul_ramificationIndex_mul_inertiaDeg` | T2 |
| semilinear automorphisms | `SemilinearAut`, `baseAut` | T3 |
| Galois equivariance of `ord`/`deg` | `ord_smul`, `deg_smul` | T3 |
| places over `v` form one orbit | `exists_algEquiv_smul_eq_of_restrict_eq` | T3 |
| equivariance of `e` and `f` | `ramificationIndex_eq_of_restrict_eq`, `inertiaDeg_eq_of_restrict_eq` | T3 |
| multiplicativity of `e`, `f` in towers | `ramificationIndex_eq_mul_ramificationIndex_restrict`, `inertiaDeg_eq_mul_inertiaDeg_restrict` | T3 |

## Open questions for the review

- Should the two generic orbit/index lemmas
  (`MulAction.ncard_orbit_inter_orbit_mul_card`,
  `Subgroup.exists_eq_mul_of_index_inf_eq`) be explained here or in 016? Plan:
  **016**, where the bifibre count uses them.
- Should the `Place`/`HeightOneSpectrum` bridge also cover the older
  `Place.smul`/`degZeroSMulHom` Galois action from 008 §8, or leave that to 008?
  Plan: leave the `F ≃ₐ[K] F` action to 008, keep only `SemilinearAut` here.
- Length target: ~450–550 lines, mirroring 008.
