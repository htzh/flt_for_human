# The genus-one place gate — port record

Port of the pin node
`WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem`
(FLT `anthropics/fermats-last-theorem` @ `aa2d8b3`, mathlib `v4.34.0`).
Blueprint: [../topics/riemannRoch/TOPIC-genusOnePlaceGate.md](../topics/riemannRoch/TOPIC-genusOnePlaceGate.md).

## Measured

| metric | value |
|---|---|
| pin `S_` raw lines / declaration-span | 2,288 / 2,244 |
| already in the port (vetted) | 1,212 lines / 68 declarations |
| net new | 1,032 lines / ~50 declarations |
| written library lines | **1,004** in 5 new modules |
| checker before → after | 5,699 → **5,750 identical**, 0 mismatched, 0 missing |
| consumer | exit 0 (new zone in `spec/WeierstrassCurveConsumer.lean`) |
| axioms on the headline | `[propext, Classical.choice, Quot.sound]` |
| `sorry` | none (build warnings and `grep`) |

## Modules (role per module, dependency order)

| module | role | pin lines |
|---|---|---|
| `WeierstrassCurve/Place/RRSpace.lean` | the coordinate ring's Riemann–Roch space and its dimension, and the degree/uniqueness/existence of the infinite place | 239–436, 1511–1784 |
| `WeierstrassCurve/Place/GeometricPlace.lean` | geometric point→place map, point↔place bijection, `geomDivisorSum`, `GeomAbelTheorem` | 924–1035 |
| `AlgebraicCurve/PrincipalDivisors/Count.lean` | generic Dedekind `count`/`spanSingleton` bridge and `ord = count` | 1823–1888 |
| `WeierstrassCurve/Place/UnitIdeal.lean` | unit ideal of a point/divisor, its class-group class, Abel's theorem | 1907–2076 |
| `WeierstrassCurve/GenusOnePlaceGateCentred.lean` | the headline | 2252–2288 |

`RRSpace` and `GeometricPlace` are independent (both import only
`Place/Dictionary.lean`); `UnitIdeal` imports `GeometricPlace` + `Count`; the
capstone imports all three.  No existing module was edited.

## Faithfulness

The pin `S_` file shares **all 124 declaration names** with the already-ported A1
file `S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean`, which is
already in the checker's `SOURCES`; the only new name in `SOURCES` is the genus
`Theorems/` wrapper for the headline.  Statements are transcribed verbatim; the
checker's `+51 identical` is the port's added declaration surface (the five new
modules contain 51 public/pin-named declarations, the rest being `private`
helpers already registered through the pin's private surface).

## Plan vs actual, and friction

* The subagents dispatched for the two independent first sets were stopped and
  the sets finished directly; the geometric module had been left with an
  unsynthesised `IsDedekindDomain W.CoordinateRing`.  **Cause**: the pin supplies
  this instance through its `scoped instance` activated by `p2m_open
  "WeierstrassCurve.Affine.CoordinateRing"`, while the port's copy of that scoped
  instance lives in the `WeierstrassCurve.Affine.CoordinateRing` namespace, which
  is *not* activated by `open scoped WeierstrassCurve.Affine`.  **Fix**: carry
  `[IsDedekindDomain W.CoordinateRing]` as a section variable in both
  `GeometricPlace` and `UnitIdeal` (invisible to the text-based checker).
* In the degree block (namespace `WeierstrassCurve.Affine`, after
  `end CoordinateRing`), the pin's `p2m_open` had supplied `natDegree_norm_ne_one`,
  `heightOneSpectrumOfEquation`, `heightOneSpectrumOfEquation_asIdeal` and
  `XYIdeal` unqualified; the port needed `CoordinateRing.` qualifications.
* `geomDivisorSum_eq_zero_of_isPrincipal'` must **not** `omit [InfinitePlace W]`:
  its proof uses `unitIdealOfDivisor`/`geomDivisorSum`, both of which need the
  instance.
* `Count.lean`'s `ord_ofHeightOneSpectrum_eq_count` inlines the pin's three-line
  `valation_eq_neg_log` uniformizer step rather than importing the general
  `ord_ofHeightOneSpectrum_eq_neg_log`, whose only general home in the port is the
  downstream `IsogenyEndDatum/DualEndData.lean`: importing it here would invert the
  import graph and declaring it again would clash when both are imported.
* The consumer's concrete curve is over `AlgebraicClosure ℚ`, which has no
  computable `DecidableEq`; a `private instance := Classical.decEq _` and
  `attribute [local instance]` for the curve's elliptic/Dedekind/principal-divisor
  facts were needed because the example *statements* (not only the proofs) require
  them.

## Follow-ups

* None specific to this silo.  The `CARRY-FORWARD.md` "Weierstrass place /
  Riemann–Roch / class-group API" entry is now fully closed (its dictionary,
  gate and RR/class-group/Abel blocks are all ported) and has been **removed** from
  the register, so it no longer carries forward.
