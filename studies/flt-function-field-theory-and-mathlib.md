# Survey: function-field theory in FLT and its mathlib interface

Reference survey of how the FLT formalization builds function fields of curves, how
much of that theory it develops itself, and exactly where mathlib is used. Intended as
a standing reference for future notes, apps and searches, not as prose for a general
reader.

Everything is read from the clone `~/proj/fermats-last-theorem` pinned at
`anthropics/fermats-last-theorem@aa2d8b3` (Mathlib `v4.33.0`). Citation form: `path:line`
is relative to that checkout, and is reachable at
`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3` + path + `#L<line>`;
the handful of load-bearing declarations below are linked in full. Repo conventions are
those of [../AGENTS.md](../AGENTS.md).

## 0. The question and the short answer

Question: FLT looks like it is built on the function-field side; how much function-field
theory does it develop in combination with mathlib?

Answer: **almost all of it.** Mathlib v4.33.0 has no curve theory — no
`AlgebraicGeometry.Curve` module, no genus, no Riemann–Roch, no Weil pairing, no
function-field places or divisors, no Serre duality. FLT supplies the entire arithmetic
curve layer itself, on a thin mathlib base, and proves it (no `sorry`, no `axiom`).
Mathlib is used at exactly two seams:

- the **scheme seam**: `Scheme`, `Scheme.functionField`, `IsIntegral`, `IsProper`,
  `SmoothOfRelativeDimension 1`, `ValuativeCriterion`;
- the **valuation/Dedekind seam**: `ValuationSubring`, `Valuation`,
  `IsDiscreteValuationRing`, `HeightOneSpectrum`, `AdicCompletion`,
  `KaehlerDifferential`.

One-sentence version: **mathlib gives the function field as a field and the underlying
algebra; FLT gives the curve.**

The most common misreading to avoid is in §10: the `Prop` classes
(`IsCurveOver`, `HasCanonicalDivisor`, `ResidueTheorem`, `FunctionFieldRiemannRoch`, …)
are a hypothesis discipline *inside* the theory, not assumptions on which the theory
rests. They are all discharged from `IsCurveOver`; see §5.

## 1. Scale and shape of the tree

Three layers matter:

- `Definitions/Def_*.lean` — types, structures, classes, statement-level `Prop`s.
- `Theorems/Thm_*.lean` — one theorem per file, a thin wrapper that imports the proof
  and closes with `p2m_exact_reverting` (defined in `P2M/Util.lean`).
- `P2M/Sol/S_*.lean` — the actual proofs, namespaced `P2MW.S_<name>`, exposing `solution`.

Counts are files/lines over the pinned checkout.

| Group (path prefix)          | defs        | statements      | proofs            | total lines |
|------------------------------|-------------|-----------------|-------------------|-------------|
| `*_AlgebraicCurve_*`         | 72 / 21,105 | 1,577 / 43,883  | 1,577 / 618,916   | 683,904     |
| `*_ModularCurve_*`           | 291 / 46,310| 7,711 / 491,908 | 7,711 / 3,369,150 | 3,907,368   |
| `*_AlgebraicGeometry_*`      | 172 / 34,383| 3,322 / 97,934  | 3,322 / 679,351   | 811,668     |
| `*_CerednikDrinfeld_*`       | 83 / 13,966 | 2,376 / 164,147 | 2,376 / 840,428   | 1,018,541   |
| `*_WeierstrassCurve_*`       | 61 / 17,899 | 1,003 / 23,330  | 1,003 / 372,091   | 413,320     |
| `*_GoodReductionJacobian_*`  | 12 / 1,984  | 674 / 26,987    | 674 / 168,067     | 197,038     |
| `*_AutomorphicForm_*`        | 106 / 17,610| 2,336 / 137,051 | 2,336 / 1,477,733 | 1,632,394   |

Whole repository: **60,474 Lean files, 13,499,321 lines** (`Definitions/` + `Theorems/` +
`P2M/`).

- Core curve groups (`AlgebraicCurve`, `ModularCurve`, `AlgebraicGeometry`): 5,402,940
  lines ≈ **40%**.
- Adding the curve-adjacent `CerednikDrinfeld`, `WeierstrassCurve`,
  `GoodReductionJacobian`: 7,031,839 lines ≈ **52%**.
- `ModularCurve` alone is the largest single block (3.9M lines), and `AlgebraicCurve` is
  the generic theory it instantiates.

Statement/proof shape:

- `Thm_AlgebraicCurve_*`: 1,577 files, 43,883 lines (avg 27.8, min 5, max 187).
- `S_AlgebraicCurve_*`: 1,577 files, 618,916 lines (avg 392; largest 13,173,
  `S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean`).
- `Thm_ModularCurve_*`: avg 63.8 lines; `S_ModularCurve_*`: avg 437 lines.

Counting recipes (see §12) — in particular, never use `… | xargs wc -l | tail -1`.

## 2. Inventory of the generic layer: `Definitions/Def_AlgebraicCurve_*.lean`

72 files, 21,105 lines. Grouped by theme; `LOC` is lines. All paths are under
`Definitions/` and start `Def_AlgebraicCurve_`.

### A. Places, valuations, local theory, completion (11 files)

| File | LOC | Role |
|---|---|---|
| `DivisorClassGroup` | 484 | **seed file**: `Place`, `ResidueField`, `deg`, `adicValuation`, `ord`, `Divisor`, `degree`, `principal`, `Pic`, `Pic0`, Galois action on places |
| `PlacesOverDVR` | 506 | places over a DVR, residue/inertia behaviour |
| `PlaceCompletion` | 529 | `Place.adicCompletion`, `adicCompletionIntegers`, absolute-value form |
| `PlaceDepth` | 161 | depth of a place in a tower |
| `PlaceEvaluation` | 86 | `Place.IsRational`, `Place.evalAt` |
| `PlaceEvaluationAlgebra` | 160 | algebra structure on place evaluation |
| `PlaceTaylorCoeff` | 93 | Taylor coefficients of a place |
| `PlacesOf` | 60 | `placesOf c U`: places realized by closed points in an open `U` |
| `AffinoidCentre` | 38 | centres of affinoid subdomains |
| `FibreResidueIdentityAlong` | 26 | residue identity along a fibre |
| `ResidueDiscs` | 270 | discs of the residue map |

### B. Curve models and base change (9 files)

| File | LOC | Role |
|---|---|---|
| `CurveModel` | 85 | **the scheme seam**: `CurveModel`, `baseToFunctionField`, `ffAlgEquiv`, `placeEquiv`, `pointEquivPlace` |
| `CurveModelConstruction` | 2,085 | `glued`, `CurveModel.ofGenerator`, `gluedFunctionFieldEquiv`, `gluedPlaceOfPoint` |
| `CurveModelSmooth` | 296 | smoothness of the constructed model |
| `CurveModelTransport` | 225 | transport of models along isomorphisms |
| `IsCurveOver` | 76 | **the curve axiom** and its consequences |
| `TwoChartIntegralModel` | 379 | integral two-chart model, `baseChange`, `fibre` |
| `TwoChartIntegralModelCharts` | 352 | chart algebras of the two-chart model |
| `KaehlerToFunctionField` | 132 | Kähler differentials of an open → function field |
| `ConstantReduction` | 127 | reduction of the constant field |

### C. Divisors, Picard, correspondences (15 files)

| File | LOC | Role |
|---|---|---|
| `DivisorPushPull` | 735 | `ramificationIndex`, `Place.restrict`, `inertiaDeg`, `pushforward`, `fiber`, `pullback`, `FundamentalIdentity`, `SumRamificationInertia` |
| `Correspondence` | 346 | divisor correspondences (the shape of a Hecke operator) |
| `GluedPic0` | 276 | `GluingData`, `GluedPic0`, `nodeUnit` |
| `GluedPic0Functoriality` | 216 | functoriality of the glued Picard group |
| `GluedPic0CrossFunctionality` | 219 | cross-functoriality |
| `GluedPic0Pushforward` | 143 | pushforward on glued `Pic0` |
| `GluedPic0SliceOps` | 98 | slice operations |
| `NodalPic0` | 94 | `NodalPic0` for nodal fibres |
| `Pic0BaseChange` | 125 | `Pic0.baseChange` |
| `Pic0Congr` | 122 | transport of `Pic0` along field isomorphisms |
| `FrobeniusEndo` | 49 | Frobenius endomorphism on divisors |
| `FrobeniusEndoPic0` | 322 | Frobenius on `Pic0`, Hecke fibre action |
| `SymmetricPower` | 128 | `SymmetricPowerPackage` |
| `UniversalDivisor` | 167 | `RelEffDivisor`, `UnivDivisorPack` on a scheme |
| `RelCartier` | 102 | `RelEffDivisor.IsCartier` |

### D. Differentials, canonical divisor, residues, duality (12 files)

| File | LOC | Role |
|---|---|---|
| `Differentials` | 85 | `Place.diffCoeff`, `ordDiff`, `IsRegularDiff`, `regularDiffs` |
| `DifferentialPushPull` | 79 | push/pull of differentials |
| `RegularDifferentials` | 46 | `regularDifferentials` |
| `PolarDifferentials` | 200 | polar differentials |
| `CanonicalDivisor` | 42 | `HasCanonicalDivisor`, `canonicalDivisorOf`, `canonicalClass`, `genus` |
| `LocalResidue` | 308 | `LocalResidueData`, `HasCanonicalLocalResidueKStar`, `HasSeparableResidue` |
| `CanonicalLocalResidueInstance` | 694 | construction of canonical local residues (v1) |
| `CanonicalLocalResidueInstanceV2` | 2,173 | v2: `CoefficientFieldSection`, `CanonicalLocalResidueDataS`, `lg37_completion`, `Lg37CompletionSection` |
| `WeilOfKaehler` | 133 | `weilOfKaehler`, `ResidueTheorem`, `WeilKaehlerAgree`, `ResiduePairingSurjective` |
| `SerrePairing` | 259 | `serrePairing` and bijectivity/flip results |
| `TateResidueCurrency` | 449 | `tateRes` and the Tate residue bookkeeping |
| `LogDeRhamH1` | 420 | `logForms`, `H1`, used on the p-adic side |

### E. Repartitions, adeles, Riemann–Roch (6 files)

| File | LOC | Role |
|---|---|---|
| `Repartitions` | 149 | `repartitions`, `repartitionsOf`, `riemannRochSpace`, `H1`, `principalRepartitions` |
| `AdelicIndex` | 435 | `LSpace`, `ell`, `adeleBdd`, `adeleSpace`, `diagonalHom`, `indexOfSpecialty`, `omegaSpace`, `residuePairing`, `RiemannGenusReachedAt`, `StichtenothGenusExists` |
| `RiemannRochRows` | 66 | `RiemannInequality`, `RiemannIndexFormula`, `WeilDualityAdelic`, `WeilDuality`, `WeilOmegaEllAgrees`, `FunctionFieldRiemannRoch` (all `Prop`s) and implication lemmas |
| `PoleDivisorPackage` | 101 | `PoleDivisorPackage`, `TranscendenceTower` |
| `CechSectionsOfDivisor` | 266 | Čech sections of a divisor |
| `CechH1PushPull` | 157 | Čech `H¹` push/pull |

### F. Jacobian, Weil pairing (3 files)

| File | LOC | Role |
|---|---|---|
| `JacobianH1Autoduality` | 337 | `H1Gm`, `H1mu`, `HomPic0Gm`, `WeilPairingData`, `autodualityEquiv`, `PrincipalPolarization` |
| `WeilDatum` | 81 | `WeilDatum`, its `pairing` and symmetry |
| `FunctionFieldWeilPairingDivisorial` | 790 | `DivisorialWeilPairingData`, `ExistsPerfectDivisorialWeilPairing` |

### G. Semistable, Deligne–Rapoport, annuli (7 files)

| File | LOC | Role |
|---|---|---|
| `SemistableModel` | 216 | `SemistableModel`, fibre shape classification |
| `SemistableCharts` | 188 | `ComponentChart`, `Annulus` |
| `SemistableChartsComap` | 358 | comap of charts |
| `StandardAnnulus` | 1,655 | `gaussValuation`, `standardAnnulus` |
| `RegularProlongation` | 84 | regular prolongation of a place |
| `TotallyDegenerateCovering` | 92 | `TotallyDegenerateCovering` |
| `TotallyDegenerateCovering_Hom` | 317 | `DegeneracyData.FiniteHom`/`Hom` |

### H. Rational function field `P¹` (3 files)

| File | LOC | Role |
|---|---|---|
| `RatFuncPlaces` | 397 | `heightOneSpectrumOfIrreducible`, `finitePlace`, `placeOfPoint`, `congrEquiv` |
| `RatFuncPlaceClassification` | 124 | `placeEquivOption` (all places of `RatFunc K`) |
| `RatFuncPlaceInfty` | 44 | `placeInfty` |

### I. Constant field and Galois base change (2 files)

| File | LOC | Role |
|---|---|---|
| `BaseChangeGalois` | 355 | Galois action under base change |
| `ConstantFieldPullback` | 272 | pullback along a constant-field extension |

### J. Analytic / archimedean extras (4 files)

| File | LOC | Role |
|---|---|---|
| `CellDissection` | 155 | cell decompositions |
| `ComplexLineIntegral` | 101 | complex line integrals used in the residue comparison |
| `ChordalProximity` | 25 | chordal proximity estimates |
| `CycleChowForm` | 140 | cycle/Chow-form bookkeeping |

The corresponding theorem/proof layer for this group is 1,577 + 1,577 files; the heaviest
sub-areas by combined lines are `Place` (289 files, 68,751), `RationalFunctionField`
(47, 51,609), `RegularProlongation` (91, 42,272), `Pic0` (107, 33,886),
`TwoChartIntegralModel` (127, 29,247).

## 3. Core definitions

### 3.1 `Place`

[`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:22-30`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L22-L30):

```lean
structure Place where
  toValuationSubring : ValuationSubring F
  algebraMap_mem' : ∀ a : K, algebraMap K F a ∈ toValuationSubring
  ne_top' : toValuationSubring ≠ ⊤
  isPrincipalIdealRing' : IsPrincipalIdealRing toValuationSubring
```

over `(K F) [Field K] [Field F] [Algebra K F]`. A `Place K F` is a nontrivial valuation
subring of `F` containing `K` that is a principal ideal ring — a DVR of `F/K`, the
algebraic surrogate for a closed point. It is deliberately **not** a `HeightOneSpectrum`
and **not** a generic `Valuation`; those are reached later.

Derived immediately (same file):

| Declaration | Line | Meaning |
|---|---|---|
| `Place.ResidueField` | 88 | `IsLocalRing.ResidueField v.toValuationSubring` |
| `Place.deg` | 90 | `Module.finrank K v.ResidueField` |
| `Place.FiniteResidue` | 92 | class: `Module.Finite K v.ResidueField` |
| `Place.heightOneSpectrum` | 95 | `IsDiscreteValuationRing.maximalIdeal _` |
| `Place.adicValuation` | 102 | `Valuation F ℤᵐ⁰`, from the height-one spectrum |
| `Place.ord` | 122 | `-(WithZero.log (v.adicValuation f)) : ℤ` |
| `Place.ofHeightOneSpectrum` | 465 | converse bridge from a Dedekind height-one prime |
| `Place.smul` / `degZeroSMulHom` | 408 | `SMul (F ≃ₐ[K] F) (Place K F)` and Galois action on divisors |

An `IsDiscreteValuationRing` instance for `v.toValuationSubring` is derived at `:73-76`
via the local lemma `ValuationSubring.not_isField_of_ne_top` (`:32`), and supplies
`exists_irreducible` / `exists_units_eq_smul_zpow_of_irreducible`, which are what `ord`
is built from.

### 3.2 `Divisor`, `Pic`, `Pic0`

Same file:

```lean
abbrev Divisor : Type _ := Place K F →₀ ℤ                     -- :179
def degree : Divisor K F →+ ℤ := …                            -- :185
def IsPrincipal (D : Divisor K F) : Prop :=                   -- :198
  ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, D v = v.ord f
def principal : AddSubgroup (Divisor K F) := …                -- :200
class HasPrincipalDivisors : Prop where                       -- :217
  exists_divisor : ∀ f : F, f ≠ 0 → ∃ D, (∀ v, D v = v.ord f) ∧ Divisor.degree D = 0
abbrev Pic : Type _ := Divisor K F ⧸ Divisor.principal …      -- :221
abbrev Pic0 : Type _ := Divisor.degZero ⧸ principal …         -- :223
```

Also here: `Divisor.degZero` (`:193`), `Pic0.mk`, `Pic0.torsion`,
`AbelJacobiCard` (the `p^{2gn}` cardinality statement for `Pic0[p^n]`), and the Galois
`SMul` on `Place`.

### 3.3 `CurveModel` — the scheme seam

[`Definitions/Def_AlgebraicCurve_CurveModel.lean:23-49`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CurveModel.lean#L23-L49):

```lean
structure CurveModel (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] where
  C : Scheme.{u}
  toBase : C ⟶ Spec (CommRingCat.of K)
  [isIntegral : IsIntegral C]
  [isProper : IsProper toBase]
  [smooth : SmoothOfRelativeDimension 1 toBase]
  ffEquiv : L ≃+* C.functionField
  ffEquiv_algebraMap : ∀ a : K, ffEquiv (algebraMap K L a) = baseToFunctionField toBase a
  placeOfPoint : closedPoints C → Place K L
  placeOfPoint_bijective : Function.Bijective placeOfPoint
  range_stalk_eq : ∀ x : closedPoints C,
    ((ffEquiv.symm : C.functionField ≃+* L).toRingHom.comp
        (algebraMap (C.presheaf.stalk x.1) C.functionField)).range =
      (placeOfPoint x).toValuationSubring.toSubring
  finset_subset_affineOpen : ∀ F : Finset C, ∃ U : C.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U
```

Reading: a mathlib scheme that is integral, proper and smooth of relative dimension 1
over `Spec K`, *plus* a chosen ring isomorphism from `L` to mathlib's `C.functionField`
(the stalk at the generic point), *plus* a bijection from closed points to `Place K L`
whose valuation ring is the image of the local ring at the point.

Supporting declarations in the same file: `baseToFunctionField` (`:18`),
`functionFieldAlgebra` (`:56`), `ffAlgEquiv` (`:59`), `placeEquiv` (`:67`),
`pointEquivPlace` (`:74`).

Reverse direction — a scheme from a function field:
`CurveModel.ofGenerator` at
`Definitions/Def_AlgebraicCurve_CurveModelConstruction.lean:1996`, built on the glued
scheme `glued` (`:135`), `gluedFunctionFieldEquiv` (`:319`),
`gluedPlaceOfPoint` (`:650`). The concrete integral scheme is `TwoChartIntegralModel`
(`Definitions/Def_AlgebraicCurve_TwoChartIntegralModel.lean:236`), with `baseChange`
(`:311`) and `fibre` (`:326`).

### 3.4 `IsCurveOver` — the curve axiom

[`Definitions/Def_AlgebraicCurve_IsCurveOver.lean:15-19`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_IsCurveOver.lean#L15-L19):

```lean
class IsCurveOver : Prop extends HasPrincipalDivisors K F where
  finiteResidue : ∀ v : Place K F, Module.Finite K v.ResidueField
  kaehler_free_rank_one : Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1
```

This is the abstract "F is the function field of a smooth proper geometrically connected
curve over K". It is a theorem-target with classical characterizations:

- `isCurveOver_iff_exists_transcendental_finiteDimensional`
  ([`Theorems/…:9`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional.lean#L15)):
  for `[PerfectField K] [Algebra.EssFiniteType K F]`,
  `IsCurveOver K F ↔ ∃ t, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ IsSeparable`.
- `isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one`
  ([`Theorems/…:9`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one.lean#L15)):
  from a scheme `C` integral and smooth of relative dimension 1 over `Spec K` and a ring
  isomorphism `F ≃+* C.functionField`.
- `instIsCurveOverRatFunc`: `IsCurveOver K (RatFunc K)`.
- `exists_genus_riemannIndex_of_isCurveOver`: existence of the Riemann index from the
  axiom (see §5).

Consequences in the same file: `hasPrincipalDivisors`, `finite_residueField`,
`instFiniteResidue`, `instFreeKaehler`, `finrank_kaehler`, `instNontrivialKaehler`,
`deg_eq_one_of_isAlgClosed`, `forall_deg_eq_one_of_isAlgClosed`.

### 3.5 Differentials, canonical divisor, genus

`Ω[F⁄K] = KaehlerDifferential K F`. From `Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean`:

- `class HasCanonicalDivisor` (`:14`): every nonzero `ω` has a divisor with
  `D v = v.ordDifferential ω`;
- `canonicalDivisorOf` (`:18`), `canonicalClass` (`:27`);
- `genus K F := (Divisor.degree (canonicalDivisorOf h) + 2).toNat / 2` (`:33`).

`Place.dCoord`, `Place.uniformizer`, `Place.ordDifferential` live in
`Definitions/Def_ModularCurve_CanonicalDivisor.lean:19,30,82` — a general-purpose
declaration living in a modular-curve file, worth remembering when searching.

### 3.6 The Riemann–Roch interface

`Definitions/Def_AlgebraicCurve_RiemannRochRows.lean` defines, as `Prop`s:

| Declaration | Line |
|---|---|
| `RiemannInequality` | 16 |
| `RiemannIndexFormula` | 20 |
| `WeilDualityAdelic` | 25 |
| `WeilDuality` | 31 |
| `WeilOmegaEllAgrees` | 38 |
| `FunctionFieldRiemannRoch` | 44 |

plus the assembly lemmas `functionFieldRiemannRoch_of_riemann_and_duality` and
`weilDuality_of_riemannIndex_of_adelic`. The analytic content lives in
`Definitions/Def_AlgebraicCurve_AdelicIndex.lean`: `LSpace`/`ell` (`:14,16`),
`adeleSpace` (`:94`), `indexOfSpecialty` (`:136`), `omegaSpace` (`:160`),
`residuePairing` (`:342`), `RiemannGenusReachedAt` (`:406`), `RiemannGenusReached`
(`:413`), `StichtenothGenusExists` (`:419`). The naming says the route: Stichtenoth's
*Algebraic Function Fields and Codes* adelic/repartition proof.

### 3.7 Weil pairing and Jacobian data

- `Definitions/Def_AlgebraicCurve_WeilDatum.lean:14`: `WeilDatum (n : ℕ)` with `D₁ D₂ f₁ f₂`,
  `ord_f₁ : ord f₁ = n * D₁`, `ord_f₂ : ord f₂ = n * D₂`, `disjoint`,
  `rational`; `pairing := evalFun f₁ D₂ / evalFun f₂ D₁` (`:38`).
- `Definitions/Def_AlgebraicCurve_JacobianH1Autoduality.lean`: `H1Gm := Pic K F` (`:32`),
  `H1mu := Pic0.torsion` (`:99`), `HomPic0Gm := AddChar (Pic0.torsion K F n) K` (`:119`),
  `structure WeilPairingData (n)` with `toHom` and `bijective` (`:170`),
  `autodualityEquiv` (`:215`), `PrincipalPolarization` (`:332`).
- `Definitions/Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean`:
  `DivisorialWeilPairingData` (`:448`), `ExistsPerfectDivisorialWeilPairing` (`:723`).

## 4. The mathlib interface

### 4.1 What mathlib actually has

- `Mathlib/AlgebraicGeometry/FunctionField.lean` (204 lines): `Scheme.functionField` =
  `X.presheaf.stalk (genericPoint X)` (an abbrev, a field only under `[IsIntegral X]`),
  `Scheme.germToFunctionField` and injectivity, `IsFractionRing` for affine opens and
  stalks, `exists_isUnit_germ_eq`. Nothing about places, divisors or genus.
- `Mathlib/NumberTheory/FunctionField.lean` (302 lines): `FunctionField F K :=
  FiniteDimensional F⟮X⟯ K`; `ringOfIntegers F K := integralClosure F[X] K` with
  `IsDedekindDomain`, `IsIntegrallyClosed`, `IsFractionRing`, `IsNoetherian`
  (separable case); constant-field extensions. An algebraic-number-theory-style Dedekind
  API, not a curve API.
- No `AlgebraicGeometry/Curve*`. Nearest neighbours: `AlgebraicGeometry/OrderOfVanishing.lean`
  (`ord`, `ordHom` at codimension-1 points) and `AlgebraicGeometry/AlgebraicCycle/Basic.lean`
  (`AlgebraicCycle X R := Function.locallyFinsupp X R`, pushforward, `Hom.residueDegree`;
  no `Divisor`, no degree, no rational equivalence).
- `Mathlib/FieldTheory/RatFunc/`: `RatFunc K`, `num`/`denom`, `map`, `AsPolynomial`
  (`C`, `X`, `eval`, `algEquivOfTranscendental`), `Degree` (`intDegree`), `Valuation`
  (`RatFunc.inftyValuation`, `CompletionAtInfty`), `Luroth`, `IntermediateField`.
- `Mathlib/RingTheory/Valuation/`: `Valuation` (Wedhorn), `ValuationSubring`, `ValueGroup`,
  `LocalSubring`, `Discrete.Basic` (`IsRankOneDiscrete`, `Uniformizer`),
  `Discrete.IsDiscreteValuationRing`, `Integral`, `RamificationGroup` (ramification and
  inertia degrees), `PrimeMultiplicity`, `FiniteField`.
- `Mathlib/RingTheory/DedekindDomain/`: `Basic`, `Ideal/Lemmas`
  (`IsDedekindDomain.HeightOneSpectrum`), `AdicValuation`
  (`HeightOneSpectrum.intValuation`, `.valuation`, `.adicCompletion`,
  `.adicCompletionIntegers`, `.adicAbv`), `IntegralClosure`, `Factorization`, `Dvr`,
  `Different`, `FiniteAdeleRing`, `SInteger`, `SelmerGroup`, `PID`. Plus
  `RingTheory/FractionalIdeal/*` and `RingTheory/ClassGroup/Basic` (`ClassGroup R`).
- `Mathlib/RingTheory/Kaehler/Basic.lean`: `Ω[S⁄R] := KaehlerDifferential R S`,
  `D : Derivation R S Ω[S⁄R]`, the universal property, `finite [EssFiniteType R S]`,
  `map`, `ker_map`. No residues, no duality.
- `Mathlib/AlgebraicGeometry/EllipticCurve/`: Weierstrass equations and group laws,
  `Affine.CoordinateRing`/`Affine.FunctionField`, division polynomials, reduction,
  `LFunction`. `Jacobian/*` here means Jacobian *coordinates*, not the Jacobian variety.

### 4.2 What mathlib lacks

Grep over `Mathlib/` at `v4.33.0`: `RiemannRoch` 0, `genus` 0, `WeilPairing` 0;
`Serre` only as Serre classes/subcategories and citations; `Divisor` only as meromorphic
divisors on `ℂ` and algebraic cycles; `Place` only as number-field `FinitePlace`;
`Picard` only as `RingTheory/PicardGroup` (invertible modules) and Picard–Lindelöf;
`residue` only as local-ring residue fields. There is no general "function field of a
curve + places + divisors" API.

### 4.3 Import counts in FLT

Over `Definitions/` + `Theorems/` + `P2M/`:

| mathlib module | files |
|---|---|
| `Mathlib.AlgebraicGeometry.FunctionField` | 45 |
| `Mathlib.NumberTheory.FunctionField` | **0** |
| `Mathlib.NumberTheory.ClassNumber.FunctionField` | **0** |
| `Mathlib.RingTheory.Valuation.*` | 196 |
| `Mathlib.RingTheory.DedekindDomain.*` | 192 |
| `Mathlib.FieldTheory.RatFunc.*` | 107 |
| `Mathlib.RingTheory.Kaehler.*` | 11 |
| `Mathlib.RingTheory.ClassGroup` (deprecated path) | 5 |
| `Mathlib.RingTheory.FractionalIdeal.*` | 4 |
| `Mathlib.AlgebraicGeometry.OrderOfVanishing` | 0 |
| `Mathlib.AlgebraicGeometry.AlgebraicCycle` | 0 |

Caveat: 1,123 of the 1,577 `S_AlgebraicCurve_*` files just `import Mathlib`, so they reach
everything transitively; direct-import counts understate usage.

`Scheme`-level usage at the seam is real: `germToFunctionField` occurs in 75
`AlgebraicCurve`-named files (518 occurrences), and `C.functionField`/`X.functionField`
about 1,400 times in the `S_AlgebraicCurve` proofs alone.

### 4.4 Ingredient by ingredient

| Ingredient | Source |
|---|---|
| function field as a field | **mathlib**: `Scheme.functionField`, `FunctionField F K`, `RatFunc`, `WeierstrassCurve.Affine.FunctionField`; FLT reuses `C.functionField` via `CurveModel` |
| place / valuation dictionary | **split**: mathlib has `Valuation`, `ValuationSubring`, `HeightOneSpectrum`, `IsRankOneDiscrete`, `Uniformizer`, `RamificationGroup`; FLT defines `Place` and `placesOf` |
| divisors, degree, principal divisors | **FLT** (`Divisor := Place →₀ ℤ`); mathlib has none for curves |
| Picard / Jacobian | **FLT** (`Pic`, `Pic0`, `Pic0BaseChange`, `JacobianH1Autoduality`); quotients of `Divisor` by principal divisors, not mathlib's `ClassGroup`/`PicardGroup` |
| differentials | **mathlib** `KaehlerDifferential`/`Ω[F⁄K]` with universal property and finiteness; FLT adds `ordDifferential`, canonical divisors, regular/polar differentials, `WeilOfKaehler` |
| adeles / repartitions | **FLT** |
| Riemann–Roch | **FLT**, from `IsCurveOver` via Stichtenoth; mathlib absent |
| residues / Serre duality | **FLT**; mathlib absent |
| Weil pairing / Tate module | **FLT**; mathlib absent |
| semistable / Deligne–Rapoport | **FLT** |

## 5. Discharge chain: how the global theorems are proved

The `Prop` classes are hypotheses of individual lemmas; each is produced from
`IsCurveOver`. The chain, with hypotheses:

1. `hasCanonicalDivisor_of_isCurveOver` — `[PerfectField K] [Algebra.EssFiniteType K F]
   [IsCurveOver K F]` ⟹ `HasCanonicalDivisor K F`.
2. `dCoordGenerates_of_isCurveOver` — same hypotheses ⟹ `∀ v, v.DCoordGenerates`.
3. `instHasCanonicalLocalResidueKStar` — `[IsCurveOver K F] [PerfectField K]` ⟹
   `HasCanonicalLocalResidueKStar K F`
   (`Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean:2149`).
4. `stichtenothGenusExists_of_isCurveOver`
   ([`Thm…:9`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.lean#L17)):
   `[PerfectField K] [EssFiniteType] [IsCurveOver K F] (hC : ConstantsAreBase K F)` ⟹
   `StichtenothGenusExists K F`.
5. `riemannGenusReached_of_stichtenothGenusExists`: `StichtenothGenusExists` +
   `WeilKaehlerAgree` + `ConstantsAreBase` ⟹ `RiemannGenusReached K F (genus K F)`.
6. `riemannIndexFormula_of_genusReached`: `(∀ …, RiemannGenusReached …)` ⟹
   `RiemannIndexFormula K F`.
7. `exists_genus_riemannIndex_of_isCurveOver`: the packaged existence form,
   `∃ γ, ∀ D, Module.Finite K (adeleSpace ⧸ adeleBddPrincipal D) ∧
   indexOfSpecialty D = ell D - (degree D + 1 - γ)`.
8. `functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver` —
   `[IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K (RatFunc K)]`, plus
   `HasCanonicalDivisor`, `DCoordGenerates`, `FiniteResidue`, separability and
   `FiniteDimensional (RatFunc K) F` ⟹ `FunctionFieldRiemannRoch K F`.
9. Residues and duality: `weilKaehlerAgree_of_residueTheorem` (from `ResidueTheorem`),
   `residueTheorem_of_isAlgClosed`,
   `residueTheorem_functionField_of_smoothOfRelativeDimension_one`,
   `serrePairing_bijective_and_flip_bijective`,
   `weilDualityAdelic_of_isAlgClosed`.
10. Modular instance: `functionFieldRiemannRoch_modularFunctionFieldBar` proves
    `FunctionFieldRiemannRoch (AlgebraicClosure ℚ) (modularFunctionFieldBar N)`.

So "Riemann–Roch is a `Prop` hypothesis" is true only at the granularity of a lemma; at
the granularity of the theory it is a theorem.

## 6. Index of major results

Paths omit `Theorems/Thm_AlgebraicCurve_`; add it plus `.lean`. All are proved.

| Result | Declaration | Line |
|---|---|---|
| Riemann–Roch, dimension form | `ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable` | 19 |
| Riemann–Roch, Čech form | `cechRiemannRoch_of_genusReached` | 12 |
| Existence of the Riemann index | `exists_genus_riemannIndex_of_isCurveOver` | 17 |
| Serre pairing bijective (+ flip) | `serrePairing_bijective_and_flip_bijective` | 21 |
| Adelic Weil duality | `weilDualityAdelic_of_isAlgClosed` | 20 |
| Residue theorem (alg. closed) | `residueTheorem_of_isAlgClosed` | 17 |
| Residue theorem from a smooth curve scheme | `residueTheorem_functionField_of_smoothOfRelativeDimension_one` | 19 |
| Weil/`Kaehler` agreement | `weilKaehlerAgree_of_residueTheorem` | 8 |
| Hasse/Weil bound (upper) | `sum_divisors_mul_card_places_lt_of_even` | 13 |
| Hasse/Weil bound (lower) | `exists_sub_le_sum_divisors_mul_card_places` | 14 |
| Abel–Jacobi cardinality | `Pic0_abelJacobiCard_genus` | 15 |
| Tate module rank `2g` (char 0) | `Pic0_finrank_rationalTateModule_eq_two_mul_genusFF_of_charZero` | 18 |
| `Pic0[n]` cardinality (char 0) | `Pic0_natCard_torsion_pow_eq_pow_two_mul_genusFF_mul_of_charZero` | — |
| Degree is a sum over places | `Divisor_degree_eq_sum` | 6 |
| Genus zero ⟹ principal | `Divisor_isPrincipal_of_genus_eq_zero` | 13 |
| Weil pairing exists | `Pic0_exists_weilPairing` | 16 |
| Weil pairing nondegenerate | `WeilDatum_pairing_ne_zero` | 11 |
| Constant-field base change | `exists_baseChange_correspondence_of_constantFieldExtension` | 14 |
| Relative Jacobian | `AlgebraicGeometry_exists_relJacobian_of_smoothOfRelativeDimension_one` | 31 |
| Semistable chart/band existence | `SemistableCovering_exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne` | 20 |

## 7. The `X₀(N)` instantiation

There are two presentations, related deliberately.

### 7.1 The q-expansion fields

- `Definitions/Def_ModularCurve_X0.lean:250`: `modularFunctionField N = ℚ(j(q), j(q^N))`.
- `Definitions/Def_ModularCurve_X0.lean:305`: `modularFunctionFieldFull N = ℚ(j(q^d) : d ∣ N)`.
  Both are `IntermediateField ℚ (LaurentSeries ℚ)`.
- `ModularCurve.functionFieldGeneration`
  ([`Thm…:8`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_functionFieldGeneration.lean#L8))
  proves `modularFunctionFieldFull N = modularFunctionField N`; see
  [`math/010-function-field-generation.md`](../math/010-function-field-generation.md).
- Base change / level structure: `modularFunctionFieldC K N`
  (`Def_ModularCurve_JqCoeff.lean:61`), `modularFunctionFieldBar N` over
  `AlgebraicClosure ℚ` (`Def_ModularCurve_ArithmeticGalois.lean:111`),
  `qExpFunctionFieldC K Γ` (`Def_ModularCurve_X1.lean:101`),
  `xHFunctionFieldBar` (`Def_ModularCurve_XH.lean:123`).

### 7.2 Every modular `CurveModel` uses a q-expansion field

| Site | Declaration | `L` |
|---|---|---|
| `Def_ModularCurve_DRModelPackage.lean:51` | `M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p)` | q-expansion |
| `Def_ModularCurve_DRModelPackage.lean:55` | `Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p)` | base change |
| `Def_ModularCurve_DRModelPackage.lean:90` | `ratModel : CurveModel κ (RatFunc κ)` | special fibre |
| `Def_ModularCurve_DRModelPackageLevel.lean:80` | `Meta : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀*q))` | level `N₀*q` |
| `Def_ModularCurve_DRModelPackageLevel.lean:142` | `Mfib : CurveModel κ ↥(modularFunctionFieldC κ N₀)` | residue field |
| `Def_ModularCurve_XHDRModelAtP.lean:93` | `Meta : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)` | level-lowered |
| `Def_ModularCurve_XHDRModelAtP.lean:181` | `Mfib : CurveModel (ResidueField A) ↥(qExpFunctionFieldC …)` | special fibre |

The scheme is built by `TwoChartIntegralModel` from the q-expansion field; places are
`placeOfPoint`, matched against concretely defined q-expansion places (e.g.
`qExpFrobeniusPlaceModL`); place degrees are computed on the q-expansion side
(`Thm_ModularCurve_deg_eq_one_modularFunctionFieldC.lean:8`).

### 7.3 Bridge theorems

- `qExpFunctionFieldC ℚ (Gamma0 M) = modularFunctionFieldFull M`
  ([`Thm…:13`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull.lean#L13)),
  referenced by 110 files — the main DR↔XHDR dictionary.
- `qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd`: same for `p ∤ M`.
- `modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0`: the inclusion.
- `IgusaScheme_exists_curveModel_genericFibre_iso_and_galoisCompat`: a `CurveModel` over
  `modularFunctionFieldBar N` whose `pointEquivPlace` is equivariant for
  `arithmeticGalois (modularFunctionFieldFull N)`.
- `IgusaScheme_coeffEmb_sub_mem_nonunits_pointEquivPlace_ofGenerator_of_chartPin`:
  `coeffEmb` of elements of `modularFunctionFieldFull` lie in the valuation subring of the
  corresponding place, with prescribed residue.
- `DRLevel_exists_curveModel_iso_fibre0_chartPin`: a `CurveModel κ ↥(modularFunctionFieldC κ N₀)`
  isomorphic to the Deligne–Rapoport special fibre.

### 7.4 The automorphic field is a separate, unbridged track

`automorphicField Γ ⊂ FractionRing holRing`
(`Definitions/Def_ModularCurve_AutomorphicField.lean:150`) carries its own
`IsCurveOver ℂ (automorphicField Γ)` and a place dictionary `ℍ → Place ℂ (automorphicField Γ)`.
It is used for the Čerednik–Drinfeld level-lowering step. **No file mentions both
`automorphicField` and `qExpFunctionFieldC`** — the two models are not bridged.

### 7.5 Where `functionFieldGeneration` enters

The generation fact is consumed at the refinement boundary:
`functionFieldGeneration` feeds `IgusaScheme.exists_mul_mem_adjoin_jFull_jqN`
([`Thm…:10`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_IgusaScheme_exists_mul_mem_adjoin_jFull_jqN.lean#L10))
and the `hdeg : relfinrank … = dedekindPsi N` hypothesis of the CharP/fibre-model
packages (`Thm_ModularCurve_CharPModel_exists_fibreModel_cuspChart.lean:18`). So on the
scheme side it is an *input*, not a consequence.

Centrality: `PROOF-PATH.md` calls the `p ≥ 17` Eisenstein-ideal/irreducibility step —
`X₀(N)`, its Jacobian and Néron model, the cuspidal subgroup, the Eisenstein quotient —
"by far the largest part" of irreducibility, and the `CurveModel`/places layer is its
substrate. `CurveModel` is mentioned by 3,693 of 29,511 theorem files.

## 8. Verification status

- `grep` for `sorry` over `Definitions/`, `Theorems/`, `P2M/`, `verification/`: **0**
  genuine occurrences. The only three textual hits are
  `verification/comparator/Challenge.lean:6,9,14`, the comparator's deliberate
  challenge/solution file.
- No `axiom` or `opaque` declarations.
- `FinalCheck.lean:4-5` runs `#guard_msgs in #print axioms fermat_last_theorem`, pinning
  the dependency to `[propext, Classical.choice, Quot.sound]`;
  `verification/comparator/config.json` lists exactly those three as `permitted_axioms`.
- 1,824 files contain `#print axioms`; this is verification output, not assumptions.

## 9. Entry points

Generic curve theory, in reading order:

1. `Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean` — `Place`, `Divisor`, `Pic`, `Pic0`.
2. `Definitions/Def_AlgebraicCurve_IsCurveOver.lean` — the curve axiom.
3. `Definitions/Def_AlgebraicCurve_CurveModel.lean` +
   `…CurveModelConstruction.lean` — the scheme seam.
4. `Definitions/Def_AlgebraicCurve_AdelicIndex.lean` +
   `…RiemannRochRows.lean` — the adelic/Riemann–Roch interface.
5. `Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean`, `…LocalResidue.lean`,
   `…SerrePairing.lean`, `…WeilOfKaehler.lean` — differentials and duality.
6. `Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver.lean`
   and its `P2M/Sol/S_…` proof — the endgame.

`X₀(N)`: start from `math/010-function-field-generation.md`, then
`Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull.lean`, then
`Def_ModularCurve_DRModelPackage.lean` and `Def_ModularCurve_XHDRModelAtP.lean`.

## 10. Misconceptions to avoid

- **Do not** say the global curve theorems are assumed. The `Prop`s are a hypothesis
  discipline discharged from `IsCurveOver` (§5).
- **Do not** say FLT uses mathlib's function-field API. It imports
  `Mathlib.NumberTheory.FunctionField` zero times; it does use
  `Scheme.functionField` at the scheme seam.
- **Do not** conflate mathlib's `ClassGroup`/`PicardGroup` with FLT's `Pic`/`Pic0`.
- **Do not** assume the modular curve is presented by the automorphic field of the upper
  half plane; every `CurveModel` uses a q-expansion Laurent-series field, and the
  automorphic track is unbridged (§7.4).
- **Do not** trust `… | xargs wc -l | tail -1` for layer sizes (§12).

## 11. Citation index

Pinned tree: <https://github.com/anthropics/fermats-last-theorem/tree/aa2d8b3>.

Load-bearing declarations:

- `Place` — [Def_AlgebraicCurve_DivisorClassGroup.lean#L22-L30](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L22-L30)
- `Divisor`, `degree`, `HasPrincipalDivisors`, `Pic`, `Pic0` — [#L179-L224](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L179-L224)
- `Place.ofHeightOneSpectrum` — [#L465](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L465)
- `CurveModel` — [Def_AlgebraicCurve_CurveModel.lean#L23-L49](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CurveModel.lean#L23-L49)
- `CurveModel.ofGenerator` — [Def_AlgebraicCurve_CurveModelConstruction.lean#L1996](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CurveModelConstruction.lean#L1996)
- `TwoChartIntegralModel` — [Def_AlgebraicCurve_TwoChartIntegralModel.lean#L236](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TwoChartIntegralModel.lean#L236)
- `IsCurveOver` — [Def_AlgebraicCurve_IsCurveOver.lean#L15-L19](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_IsCurveOver.lean#L15-L19)
- `HasCanonicalDivisor`, `genus` — [Def_AlgebraicCurve_CanonicalDivisor.lean#L14-L36](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean#L14-L36)
- `ResidueTheorem` — [Def_AlgebraicCurve_WeilOfKaehler.lean#L107](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_WeilOfKaehler.lean#L107)
- `StichtenothGenusExists`, `RiemannGenusReachedAt` — [Def_AlgebraicCurve_AdelicIndex.lean#L406-L421](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean#L406-L421)
- `WeilDatum` — [Def_AlgebraicCurve_WeilDatum.lean#L14](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_WeilDatum.lean#L14)
- `WeilPairingData` — [Def_AlgebraicCurve_JacobianH1Autoduality.lean#L170](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_JacobianH1Autoduality.lean#L170)
- `isCurveOver_iff_exists_transcendental_finiteDimensional` — [Thm…#L9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional.lean#L15)
- `stichtenothGenusExists_of_isCurveOver` — [Thm…#L9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.lean#L17)
- `riemannIndexFormula_of_genusReached` — [Thm…#L8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_riemannIndexFormula_of_genusReached.lean#L23)
- `functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver` — [Thm…#L11](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver.lean#L14)
- `functionFieldGeneration` — [Thm_ModularCurve_functionFieldGeneration.lean#L8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_functionFieldGeneration.lean#L8)
- `qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull` — [Thm…#L13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull.lean#L13)
- `functionFieldRiemannRoch_modularFunctionFieldBar` — [Thm…#L157](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar.lean#L11)

Mathlib: [`Mathlib/AlgebraicGeometry/FunctionField.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/FunctionField.lean),
[`Mathlib/NumberTheory/FunctionField.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/FunctionField.lean).

## 12. Reproduction recipes

Layer sizes (concatenate, then count once):

```bash
cd ~/proj/fermats-last-theorem
for pre in AlgebraicCurve ModularCurve AlgebraicGeometry; do
  for d in Definitions Theorems P2M/Sol; do
    case $d in
      Definitions) pat="Def_${pre}_*.lean";;
      Theorems)    pat="Thm_${pre}_*.lean";;
      P2M/Sol)     pat="S_${pre}_*.lean";;
    esac
    printf '%s %s: %s files, %s lines\n' "$pre" "$d" \
      "$(find $d -name "$pat" | wc -l)" \
      "$(find $d -name "$pat" -exec cat {} + | wc -l)"
  done
done
```

**Do not** use `find … | xargs wc -l | tail -1`: when the file list is long, `xargs`
splits it into several `wc` invocations and each prints its own `total`, so the last line
is only the last batch. A first pass at this survey under-counted `S_AlgebraicCurve_*` by
6× exactly this way (95,443 instead of 618,916; the two batches were 523,473 and 95,443).

Assumption audit:

```bash
grep -rn --include='*.lean' 'sorry' Definitions Theorems P2M verification
grep -rhE '^\s*axiom ' Definitions Theorems P2M | wc -l
```

Mathlib gaps:

```bash
cd .lake/packages/mathlib/Mathlib
for t in RiemannRoch WeilPairing genus 'AlgebraicGeometry/Curve'; do
  printf '%-24s ' "$t"; grep -rli "$t" --include='*.lean' . | wc -l
done
```
