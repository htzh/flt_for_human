# PORTING — the Weierstrass genus-one place gate (`exists_genusOnePlaceGate_isCentred_and_abelTheorem`)

Planning record for the port of the pin node

```
WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
```

Pin `anthropics/fermats-last-theorem` at `aa2d8b3`, mathlib `v4.34.0`.
Target file:

```
P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean
Theorems/Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean
```

## 1. Measured cone

| metric | value |
|---|---|
| `S_` raw lines | 2,288 |
| `S_` declaration-span lines | 2,244 |
| boilerplate (imports/attrs/`p2m_*`) | 44 |
| declarations | 124 |
| `Thm_` wrapper | 31 raw / 1 declaration |
| already in the port (vetted substitutions) | 1,212 lines / 68 declarations |
| §7.4 binder-spelling clashes (port has the general form) | 3 |
| **net new math** | **1,032 lines / ~50 declarations** |

The pin `S_` file shares **all 124 declaration names** with
`S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean` (A1, 2,248 raw /
2,202 span).  It is A1's dictionary plus A1's deferred Riemann–Roch / class-group /
Abel block, capped by the genus-one headline.  The port already carries the A1
dictionary in `WeierstrassCurve/Place/Dictionary.lean` (+ `FunctionFieldQuadratic`,
`FunctionFieldFinite`, `PlaceCalculus`, `AlgebraicCurve/P1/Dictionary`,
`AlgebraicCurve/Canonical/WeilDifferential`), so the work is exactly the block the
carry-forward register had marked deferred, now taken by this consumer (the entry
is closed and has been removed from the register).

`port_advise --nodes '<node>'` (genus alone): 68 substitutions / ≈1,222 pin lines;
66 importable, 2 only port-private (`ne_arith`, `two_mul_min_arith`, both in
`Place/Dictionary.lean` — promote or keep local).  `port_plan` budget: raw 2,288,
declaration lines 2,244, vetted in-port 1,212, NET NEW 1,032, no siblings, layer 0.

Regeneration:

```bash
cd tools/deps
python3 port_advise.py --nodes WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem \
  --json build/genus_advise.json
python3 port_plan.py --json build/genus_advise.json
python3 frontier.py --target WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem --no-rank
```

## 2. Route audit (mathlib first)

**Reuse wins (mathlib).**  The RR space is built on the affine-Point basis family,
so none of the pin's `Def_EllipticCurve_ValuationInfty` copy is needed:

* `smul_basis_eq_zero`, `exists_smul_basis_eq`, `smul_basis_mul_Y`,
  `degree_norm_smul_basis`, `degree_norm_ne_one`, `natDegree_norm_ne_one`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`).

The class-group/count block reuses the mathlib Dedekind factorization API:

* `FractionalIdeal.count_well_defined`, `count_maximal`, `count_mul`, `count_zpow`,
  `count_one`, `count_zero`, `finprod_heightOneSpectrum_factorization`
  (`Mathlib/RingTheory/DedekindDomain/Factorization.lean`);
* `FractionalIdeal.isPrincipal_iff`, `spanSingleton_ne_zero_iff`,
  `exists_eq_spanSingleton_mul`, `spanSingleton_mul_spanSingleton`,
  `coeIdeal_span_singleton` (`Mathlib/RingTheory/FractionalIdeal/Operations.lean`).

**Recorded negatives (searched, not found in mathlib).**

* `FractionalIdeal.count_spanSingleton` — new.
* `FractionalIdeal.finprod_heightOneSpectrum_count` — new (mathlib has only the
  factorization form, not the count-form reassembly).
* `FractionalIdeal.eq_of_count_eq` — new.
* `AlgebraicCurve.Place.ord_ofHeightOneSpectrum_eq_count` — new (the port's
  `ord_ofHeightOneSpectrum_eq_neg_log` plus `count_spanSingleton`).
* `WeierstrassCurve.Affine.isFinitePlace_ofHeightOneSpectrum` and
  `infinitePlace_ne_ofHeightOneSpectrum` — not in the port.

**Already ported and imported (do not re-prove).**  `placeOfEquation`,
`IsFinitePlace`, `heightOneSpectrumOfEquation`, `isFinitePlace_iff_exists_placeOfEquation`,
`isFinitePlace_placeOfEquation`, `placeOfEquation_injective`, `deg_placeOfEquation`,
`InfinitePlace`, `isElliptic_Δ_ne_zero`, `ord_X_neg_of_not_isFinitePlace`,
`two_mul_ord_eq_of_not_isFinitePlace`, `two_mul_ord_Y_eq_three_mul_ord_X`,
`exists_equation`, `degree_norm_ne_one`/`natDegree_norm_ne_one`,
`ord_ofHeightOneSpectrum_eq_neg_log` (general form in
`AlgebraicCurve/PrincipalDivisors/RatFuncDegree.lean` and
`WeierstrassCurve/IsogenyEndDatum/DualEndData.lean`), the whole gate/Pic0 dictionary
(`GenusOnePlaceGate.lean`: `GenusOnePlaceGate`, `pointEquivPlace`, `placeOfPoint`,
`divisorSum`, `pointDivisor`, `pointClass`, `AbelTheorem`, `genusOnePic0Equiv`,
`GenusOnePlaceGate.IsCentred`), and `CoordinateRing.XYIdeal'`.

**§7.4 clashes.**  `mem_iff_ord_nonneg` (port: `AlgebraicCurve/Defs/PushPull.lean`,
general `Place K F`), `polyToFunctionField_apply` (`FunctionFieldQuadratic.lean`),
`adjoin_yCoord_eq_top` (`FunctionFieldFinite.lean`).  Take the port's binders; do not
re-spell.  The pin's private `algebraMap_eq_mk_C_C_s18priv` is the port's public
`CoordinateRing.algebraMap_eq_mk_C_C` (`Place/Dictionary.lean`).

## 3. Dedup

* The pin repeats the place dictionary in ~18 `S_` files; the port already made it
  one home (`Place/Dictionary.lean`).  This effort adds no new copy.
* The count block (`count_spanSingleton` etc.) is generic Dedekind theory: one home
  in `AlgebraicCurve/PrincipalDivisors/`, not in a Weierstrass module.
* The single declaration shared with the sibling silo
  `exists_intermediateField_...` is `algebraMap_eq_mk_C_C`, already importable from
  `Place/Dictionary.lean` — do not re-prove it.

## 4. Module layout (role per module)

| module | role | pin lines |
|---|---|---|
| `WeierstrassCurve/Place/RRSpace.lean` | the coordinate ring's Riemann–Roch space, its basis/finrank, and the degree/uniqueness of the infinite place | 239–436, 1511–1784 |
| `WeierstrassCurve/Place/GeometricPlace.lean` | the geometric map point → place, the point↔place bijection, `geomDivisorSum`, `GeomAbelTheorem` | 924–1073 |
| `AlgebraicCurve/PrincipalDivisors/Count.lean` | generic Dedekind count lemmas and `ord = count` | 1823–1888 |
| `WeierstrassCurve/Place/UnitIdeal.lean` | the unit ideal of a point/divisor, its class-group class, and Abel's theorem | 1907–2076 |
| `WeierstrassCurve/GenusOnePlaceGateCentred.lean` | the headline | 2252–2288 |

Dependency DAG: `RRSpace` and `GeometricPlace` are independent (both only import
`Place/Dictionary.lean`); `Count` is independent; `UnitIdeal` imports
`GeometricPlace` + `Count`; the capstone imports `UnitIdeal` + `RRSpace` (for
`instInfinitePlace`).  No existing module is edited.

Namespaces follow the pin: `WeierstrassCurve.Affine.CoordinateRing` (with
`namespace RRSpace`) for the RR block, `WeierstrassCurve.Affine` for the degree,
geometric and unit-ideal blocks, `FractionalIdeal` / `AlgebraicCurve.Place` for the
count block.

## 5. Work orders / sets

* **SET-1** `WeierstrassCurve/Place/RRSpace.lean` — the RR space + infinite place.
  Independent.
* **SET-2** `WeierstrassCurve/Place/GeometricPlace.lean` — the geometric place.
  Independent of SET-1.
* **SET-3** `AlgebraicCurve/PrincipalDivisors/Count.lean` +
  `WeierstrassCurve/Place/UnitIdeal.lean` — the count/class-group/Abel block.  Needs
  SET-2.  Written only after SET-2 is reviewed.
* **Capstone** `WeierstrassCurve/GenusOnePlaceGateCentred.lean` — the headline, the
  `IsCentred` proof and `AbelTheorem` discharge.  The reviewer writes it.

## 6. Risk register

| risk | status |
|---|---|
| RR-space `finrank_eq` defeq over `degreeLT × degreeLT` | expected low: mathlib `degreeLT.basisProd` + `LinearEquiv.ofInjective` |
| `mem_iff_natDegree_norm_le` `nlinarith` over `WithBot ℕ`/`ℤ` casts | expected low: pin proof transcribes |
| class-group `count_*` API argument-order drift | possible; use the mathlib signatures directly |
| `instInfinitePlace` instance-search cost | watch; supply explicit instances if search times out |
| namespace collision with the pin's many repeated `variable` blocks | port keeps pin namespaces, disjoint files |
| `#print axioms` sees a `sorry` inside a `def`/`class` | work definitions bottom-up; count `sorry`s from build warnings |

Predicted non-events: no new mathlib gap in the RR basis family; no instance diamond
(the port carries the `InfinitePlace` class already).

## 7. Verification recipe

1. Edit loop per file:
   `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` (≤ 90 s).
2. `lake build <module>` when a file compiles (serialize with `flock`).
3. `python3 spec/check_flt_statements.py` after SOURCES/PORT_FILES are extended —
   target `0 mismatched / 0 missing`.
4. `lake env lean spec/WeierstrassCurveConsumer.lean` with the new zones — exit 0.
5. `#print axioms` on the headline — `[propext, Classical.choice, Quot.sound]`.
6. No `sorry` (from the build warnings, not a prose grep).

## 8. Closing

**Done 2026-10-05.** Written: 1,004 library lines in the five modules above, plus a
consumer zone in `spec/WeierstrassCurveConsumer.lean` and the `SOURCES`/`PORT_FILES`
wiring.  Checker `5,699 → 5,750 identical, 0 mismatched, 0 missing`; consumer exit
0; `#print axioms` on the headline `[propext, Classical.choice, Quot.sound]`; no
`sorry`; full `lake build FLTForHuman` green (9,290 jobs).  The "Weierstrass place /
Riemann–Roch / class-group API" entry is fully closed and has been removed from
`CARRY-FORWARD.md`.  Record:
[../../logs/genus-one-place-gate-port.md](../../logs/genus-one-place-gate-port.md).
