# The basic objects: elliptic curves, modular curves, modular forms

**Status (snapshot, 2026-10-02).** A cross-subject reference for the *objects* the port
and its neighbours actually manipulate in the elliptic-curve / modular-curve /
modular-form corner of FLT, and for the theory stack under each presentation. It is
written against pin `anthropics/fermats-last-theorem@aa2d8b3` (its mathlib is
`db584cd6…`, Lean `v4.33.1`), the port `lean/FLTForHuman` + `lean/Reserve` (mathlib
`v4.34.0`), and mathlib `v4.34.0` itself. It complements, rather than repeats:

* [flt-function-field-theory-and-mathlib.md](flt-function-field-theory-and-mathlib.md)
  — the generic curve layer (`Place`, `Divisor`, `CurveModel`, `IsCurveOver`,
  Riemann–Roch) and its mathlib seam;
* [elliptic-weierstrass-tate-scout.md](elliptic-weierstrass-tate-scout.md) — the
  port cost of the elliptic-curve cluster;
* [hecke-operator-survey.md](hecke-operator-survey.md) and
  [eichler-shimura-scout.md](eichler-shimura-scout.md) — the Hecke/period stacks.

The question here is narrower and more structural: **when the formalization says
"elliptic curve", "modular curve", "modular form", what type is it, at what level of
concreteness, and what is underneath it?**

## 0. The short answer

None of the three subjects is one type. Each appears in several **presentations**, and
the choice of presentation is the load-bearing decision in every proof:

| stratum | what the object is | elliptic curve | modular curve | modular form |
|---|---|---|---|---|
| **P0 equation** | coefficients in a ring | `WeierstrassCurve R` + `IsElliptic` | — (no equation; `Φ_N` is the closest algebraic handle) | — |
| **P1 points** | a set with a group law | `Affine.Point` / `Projective.Point` / `Jacobian.Point` | cusps; `JZero` points | — |
| **P2 function field** | a field + places + divisors | `Affine.FunctionField`, `Place`, `Pic0` | `modularFunctionField N`, places, `Pic0` | modular *functions* (weight 0) and units; weight-*k* forms only through their q-expansions |
| **P3 scheme / model** | a scheme + structure map | `ProjModel`, Néron model | `CurveModel` (Igusa, Deligne–Rapoport, XHDR) | section of `ω^k` over the moduli stack (Katz) |
| **P4 local series** | completions / power series | `adicCompletion`, formal group, Tate curve, `PeriodPair` | q-expansion places, Laurent series | `QExpansion`, `qCoeff`, Eisenstein/ζ |
| **P5 arithmetic** | extra structure on the above | Tate module, Galois rep, reduction | Hecke correspondences on `Pic0`, Frobenius | Hecke algebra, eigenforms, Nebentypus |

The single most important asymmetry is this:

> **An elliptic curve arrives with a concrete equation (P0/P1) and is then handed to the
> abstract curve layer (P2/P3). A modular curve has no equation anywhere in the
> formalization: it is *manufactured* from a field of q-expansions and a place
> dictionary (P4 → P2), and only then given a scheme (P3). Modular forms are the
> bridge between the two worlds: an analytic function on the upper half plane (P4)
> whose q-expansion is the object the Hecke algebra and the algebraic side both act
> on — and at weight 0 that function *is* an element of the modular function field (P2).**

The pin says this in one sentence, about `X₀(N)`: "The formalization has no Riemann
existence theorem and no compact Riemann surface. Everything happens inside a single
fixed field of Laurent series, starting from the explicit `q`-expansion of `j`"
([math/010](../math/010-function-field-generation.md) §1).

All three subjects share one substrate — the port's generic `AlgebraicCurve` layer:
`Place`, `Divisor := Place →₀ ℤ`, `Pic0`, `IsCurveOver`, `Correspondence`. That is the
common bottom of the stack, and it exists because mathlib has no curve theory at all
(no `Place`, no divisors, no genus, no Riemann–Roch; see
[flt-function-field-theory-and-mathlib.md](flt-function-field-theory-and-mathlib.md) §4).

## 1. Elliptic curves

### 1.1 P0/P1 — mathlib supplies the concrete curve and its points

The whole bottom of the elliptic-curve stack is **mathlib**, unchanged, and the port
uses it unchanged:

| object | kind | where | notes |
|---|---|---|---|
| `WeierstrassCurve R` | structure, `[CommRing R]` | mathlib `AlgebraicGeometry/EllipticCurve/Weierstrass.lean:77` | six coefficients `a₁…a₆`; `b₂/b₄/b₆/b₈`, `c₄/c₆`, `Δ`, `j` |
| `WeierstrassCurve.IsElliptic` | protected class (Prop) | same, `:367` | `IsUnit W.Δ`; the only "this is an elliptic curve" predicate |
| `VariableChange R` | structure | mathlib `VariableChange.lean:57` | a `Group` acting on curves and on points |
| normal forms | classes / inductives | mathlib `NormalForms.lean` | `IsShortNF`, the char-2/char-3 cases, `toShortNF` … |
| `Affine.Point` | **inductive** | mathlib `Affine/Point.lean:478` | `zero \| some x y (h : Nonsingular x y)`; `AddCommGroup` at `:807` |
| `Affine.CoordinateRing` | abbrev | mathlib `Affine/Point.lean:90` | `AdjoinRoot W.polynomial`, i.e. `R[X,Y]/⟨poly⟩` |
| `Affine.FunctionField` | abbrev | mathlib `Affine/Point.lean:95` | `FractionRing CoordinateRing` |
| `Projective.Point` | structure | mathlib `Projective/Point.lean:356` | weighted projective coordinates; `toAffineAddEquiv :556` |
| `Jacobian.Point` | structure | mathlib `Jacobian/Point.lean:372` | fast-arithmetic coordinates; `toAffineAddEquiv :572` |

Port additions at this level are thin: `instIsEllipticBaseChange`
(`lean/FLTForHuman/Elliptic/Basic.lean:30`) exists only because `baseChange` does not
unfold for instance search. The Frey curve is a P0 object with concrete integer
coefficients: `structure FreyPackage` with `freyCurveInt : WeierstrassCurve ℤ`
(`lean/FLTForHuman/WeierstrassCurve/Defs/FreyPackage.lean:22,88`).

The genuinely new **P0/P1** object is FLT's *universal* curve, ported in
`lean/FLTForHuman/Elliptic/Universal.lean`: `inductive Coeff` (`:36`), the generic curve
`curve : Affine (MvPolynomial Coeff ℤ)` (`:61`), and a generic point on it —
`pointedCurve : WeierstrassCurve Univ.Field` (`:104`), `affinePoint` (`:145`),
`jacobianPoint` (`:152`). This is what lets the multiplication formula be proved once,
symbolically, and then evaluated: `zsmul_eq_smulEval`
(`lean/FLTForHuman/Elliptic/JacobianMulFormula.lean:258`) specialises the universal
`n`-th multiple to coordinates in any ring. mathlib has no analogue of that layer.

### 1.2 P2 — the curve proper is FLT's function-field layer

mathlib gives `FunctionField` as an abbrev and nothing else. The place/divisor
machinery is FLT's own and the port has brought the engine across:

* `structure Place` (`lean/FLTForHuman/AlgebraicCurve/Defs/Place.lean:37`) — a
  `ValuationSubring F` with `ne_top'`, `isPrincipalIdealRing'`; API `ResidueField`,
  `deg`, `heightOneSpectrum`, `adicValuation`, `ord`;
* `abbrev Divisor := Place K F →₀ ℤ` (`Defs/Divisor.lean:25`), `class
  HasPrincipalDivisors` (`:70`), `abbrev Pic0` (`:74`), `abbrev Pic` (`:95`);
* `class IsCurveOver : Prop extends HasPrincipalDivisors K F`
  (`Defs/IsCurveOver.lean:23`) — the curve axiom, and the only thing "being a curve"
  means at this level;
* the elliptic-curve-specific bridge is **pin-only**: `class GenusOnePlaceGate`
  (`Definitions/Def_WeierstrassCurve_GenusOnePic0.lean:18`) with
  `pointEquivPlace : W.Point ≃ Place F W.FunctionField` (`:29`) and
  `divisorSum : Divisor →+ W.Point` (`:46`), i.e. `E(K) ≅ Pic⁰`. The port already
  names this as a future consumer (`lean/FLTForHuman/WeierstrassCurve/PrincipalDivisors.lean:19`).

mathlib does supply one P1→P2 bridge on its own:
`Affine.Point.toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing)`
(`Affine/Point.lean:752`), the ideal-class map, injective at `:797`.

### 1.3 P3/P4 — projective model, formal group, Tate curve: largely pin-only

* **P3.** FLT bolts a scheme-theoretic model onto mathlib's curve:
  `structure RelativeGroupLaw {A : Scheme} (f : A ⟶ Spec R)`
  (`Definitions/Def_WeierstrassCurve_ProjModel.lean:67`), `projModelCR` (`:301`),
  Galois twist (`:315`), and the bridge `IsPointsEval` (`:326`) identifying
  `T`-points with `Affine.Point`s of the base change. With `ProjModel_AddFormulas`
  (653 lines), `ProjModel_GroupLawVocabulary` (2,272) and the chart files, this is
  ~3,700 pin lines — **none ported**. A generic `WeierstrassCurve.Generic` over
  `MvPolynomial (Fin 5) K` (`Def_WeierstrassCurve_Generic.lean:17`) is also pin-only.
* **P4.** The Tate curve is a *concrete Weierstrass model over a Laurent-series ring*:
  `curve : WeierstrassCurve K := ⟨1,0,0,a₄ q,a₆ q⟩`
  (`Definitions/Def_TateCurve_QSeries.lean:185`), with `pointX`/`pointY` as q-Laurent
  sums (`Def_TateCurve_PointSeries.lean:179,181`), `tateLaurent : WeierstrassCurve
  (LaurentSeries K)` (`Def_ModularCurve_TateFormal.lean:86`), and the torsion
  parametrisation `tateTorsionPoint :905` / `tateTorsionEquiv :984`. The whole
  `TateCurve` block (57 nodes) is **unported**. The formal-group block
  (`FormalGroupLaw.lean`, `FormalGroup.lean`) is likewise unported; the port has only
  the ω/EDS side (`lean/FLTForHuman/Elliptic/Omega.lean:49`).
* **Reduction.** mathlib has `IsIntegral`, `IsMinimal`, `reduction`,
  `HasGoodReduction` (`Reduction.lean:59,276,318,325`); FLT's own vocabulary
  (`reductionMod`, `traceOfFrobenius`, `IsSemistableModel`, `IsModular`,
  `lean/FLTForHuman/WeierstrassCurve/Defs/Modularity.lean:59–84`) is ported, but
  `Semistability.lean`, `ReductionMap.lean`, `ReduceHom.lean` and
  `ZeroComponentReduction.lean` are pin-only.
* **Torsion.** The EDS/ω/division-polynomial stack is the port's elliptic-curve
  success: `inductive Param`, `universalNormEDS`, `ωe`, `invar`, `ψc`, the `MulFormula`
  layer, and the bridge `smul_eq_zero_iff_evalEval_ψ`
  (`lean/FLTForHuman/Elliptic/Bridge.lean:53`), culminating in
  `card_nTorsion` (`Elliptic/TorsionCard.lean:1131`). The isogeny side (Vélu,
  `IsogenyEndDatum`, dual isogenies, Drinfeld, Tate module) is pin-only.

**Theory stack.** P0/P1 sit on mathlib's `EllipticCurve` tree alone. P2 sits on the
port's `AlgebraicCurve` engine (places, divisors, `Pic0`, the place-degree API) which
itself sits on mathlib `Scheme.functionField`, `Valuation`, `DedekindDomain`,
`KaehlerDifferential`. P3/P4 sit on mathlib `Scheme`/`IsProper`/`SmoothOfRelativeDimension 1`
plus FLT's own construction; the Tate/formal layers additionally need mathlib's
`PowerSeries`/`LaurentSeries` and the complete-nonarchimedean vocabulary.

## 2. Modular curves

### 2.1 There is no equation

No file in the pin or the port defines `X₀(N)` by a polynomial, a scheme built from one,
or a quotient of the upper half plane. The object that *is* `X₀(N)` at the working level
is a **function field presented as an intermediate field of Laurent series**:

* `modularFunctionField N : IntermediateField ℚ (LaurentSeries ℚ)` = `ℚ(j(q), j(q^N))`
  (pin `Definitions/Def_ModularCurve_X0.lean:250`; port
  `lean/FLTForHuman/ModularCurve/Defs/Fields.lean:42`);
* `modularFunctionFieldFull N = ℚ(j(q^d) : d ∣ N)`
  (pin `X0.lean:305`; port `Fields.lean:137`), with
  `functionFieldGeneration` proving the two are equal
  ([`Thm_ModularCurve_functionFieldGeneration.lean:8`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_functionFieldGeneration.lean#L8));
* the generator is an explicit Laurent series
  `jq : LaurentSeries ℚ := q⁻¹ * jNum` (pin `X0.lean:157`; port `Defs/Jq.lean:110`),
  with `jqN := qExpand ℚ N jq` (`Jq.lean:193`) and the substituted/twisted conjugates
  `TS K e u = j(u q^e)` (port `Defs/TS.lean:39`).

Base change and level structure are then *more intermediate fields of the same kind*:
`modularFunctionFieldC K N` (`Defs/JqCoeff.lean:74`), `modularFunctionFieldBar N :=
laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)`
(`lean/FLTForHuman/ModularCurve/Defs/ArithmeticGalois.lean:110`), and the level-`Γ`
field `qExpFunctionFieldC K Γ` (port `ModularCurve/JqIntegralRatios.lean:92`; pin
`Def_ModularCurve_X1.lean:101`), the `K`-subfield of `LaurentSeries K` generated by
ratios of integral `q`-expansions of `Γ`-forms. The three classical curves are then the
*same construction with different `Γ`*, and there is no separate declaration for any
of them:

* `X₀(N)` is `qExpFunctionFieldC K (Gamma0 N)` — no own name;
* `X₁(N)` is `x1FunctionFieldC K M = qExpFunctionFieldC K (Gamma1 M)`
  (port `X1/Defs.lean:75`);
* `X_H` is `xHFunctionFieldC K M H = qExpFunctionFieldC K (GammaH M H)` — **pin-only**
  (`Def_ModularCurve_XH.lean:76`), including its base change
  `xHFunctionFieldBar` (pin `XH.lean:123`); the port has no `X_H`.

The dictionary that identifies the Deligne–Rapoport level-`N` presentation with the
`X_H` presentation is exactly an equality of intermediate fields,
`qExpFunctionFieldC ℚ (Gamma0 M) = modularFunctionFieldFull M`
([`Thm…:13`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull.lean#L13)).
The one genuinely *concrete* algebraic object attached to `X₀(N)` is its modular
polynomial: `structure ModularPolynomialData N`
(`lean/FLTForHuman/ModularCurve/Defs/Polynomial.lean:31`) carries a monic
`Φ : Polynomial (Polynomial ℤ)` of `natDegree (dedekindPsi N)` with
`Φ.eval₂ evalAtJ (jqN N) = 0`; that `Φ` *is* `Φ_N`. (The classical `phiTwo`/`phiThree`
are pin-only, `Def_ModularCurve_ClassicalModularPolynomials.lean:18,37`.)

The name "curve" is earned only by an `IsCurveOver` instance on such a field, and the
geometry is recovered through **places**. Cusps are places: `cuspInfty : Place ℚ
(modularFunctionField N)` (`Defs/QAdicPlace.lean:351`), `cuspInftyFull` (`:360`),
`cuspInftyBar` (`Defs/AtkinLehner.lean:111`), and `IsCusp j v := j ∉
v.toValuationSubring` (`Defs/QAdicPlace.lean:372`). The q-expansion is the local
parameter at them: `ord_qInftyPlaceBar`
(`lean/FLTForHuman/ModularCurve/Analytic/CuspBookkeeping.lean:78`) computes the order at
the infinity place from the Laurent series, `ord_cuspInftyBar` (`:108`) and
`ord_cuspInftyBar_coeffEmb_qExpand` (`:120`) transport it along `q ↦ q^d`, and
`cuspZeroBar_ne_cuspInftyBar` (`:168`) separates the two cusps. So the concrete
q-expansion side and the abstract place side meet at one lemma, and that lemma is what
turns "field of series" into "curve".

### 2.2 P1/P2 — Jacobian, cusps, Hecke correspondences

Once the field is a curve, the arithmetic is read off it:

* **Jacobian.** `abbrev JZero N := Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N)`
  (`ArithmeticGalois.lean:114`); `JOne` is the same for `x1FunctionFieldBar`
  (`X1/Defs.lean:133`). There is no separate Jacobian *variety*: `J₀(N)` is degree-zero
  divisor classes modulo principal divisors on the abstract field.
* **Cusps as divisors.** `cuspidalDivisor` and its degree-zero class
  `cuspidalClass : JZero N` (`Defs/CuspidalClass.lean:40,47,63`) — this is the
  cuspidal subgroup element the Eisenstein-quotient argument uses. The two cusps are
  related by the Fricke involution: `IsFrickeAut`/`frickeInvolution`
  (`Defs/AtkinLehner.lean:34,39`), their level-`N` versions
  (`IsFrickeAutFull`/`frickeInvolutionFull`, `:62,70`), the base-changed
  `frickeInvolutionBar` (`Defs/CuspidalClass.lean:26`) and
  `cuspZeroBar := frickeInvolutionBar • cuspInftyBar` (`:38`). The two-cusp dichotomy
  is `eq_cuspInftyBar_or_eq_cuspZeroBar`
  (`Analytic/CuspDichotomy.lean:252,331`).
* **Degeneracy maps.** `towerInclBar`/`towerSubstBar`
  (`Defs/DegeneracyTower.lean:31,58`), the level-raising/lowering pair that the Hecke
  `α`/`β` operators are built from (`heckeAlphaBar_eq_towerInclBar` /`…_eq_towerSubstBar`,
  `:81,84`).
* **Hecke operators as divisor correspondences.** The generic shape is
  `correspondence : Pic0 K F →+ Pic0 K F` built from `pullbackAlong`/`pushforwardAlong`
  (`lean/FLTForHuman/AlgebraicCurve/Defs/Correspondence.lean:126,158,242`); the modular
  instantiation is `heckeOperatorBar ℓ : Module.End ℤ (JZero N)`
  (`ModularCurve/Defs/HeckeModule.lean:35`), with the abstract Hecke algebra
  `HeckeAlg := MvPolynomial Nat.Primes ℤ` (`:71`) and its action `heckeModuleBar`
  (`:122`). `HeckeOperatorsCommuteBar` (`:44`) is the commutativity input to the
  irreducibility route — the subject of [math/009](../math/009-hecke-jacobian-commute.md).
* **The concrete P¹ model.** `ProjectiveLine R` (`Defs/ProjectiveLine.lean:66`), built
  as unimodular row vectors modulo units (`IsUnimodularRow :37`, `UnimodularRow :52`),
  is the one *concrete* projective variety in this corner. It is the `j`-line model of
  `X(1)`, not of `X₀(N)`.

### 2.3 P3 — the scheme layer is the big gap

The pin constructs actual schemes from these fields and matches them point-by-point to
places. `structure CurveModel K L` (`Definitions/Def_AlgebraicCurve_CurveModel.lean:23`)
bundles a scheme `C`, a `K`-algebra structure on `L`, and an isomorphism
`L ≃ C.functionField`, with the dictionary `placeEquiv : closedPoints C ≃ Place K L`
(`:67`) and `pointEquivPlace` (`:73`). From that, `CurveModelConstruction` (`glued`,
`CurveModel.ofGenerator`) and `TwoChartIntegralModel` build the two-chart integral model
that every modular instance uses.

On top of it the pin has, all **pin-only**: `DRModelPackage`/`DRModelPackageLevel`
(Deligne–Rapoport models), `CharPModel*`/`FibreModel*` (characteristic-`p` fibres),
`XHDRModelAtP` (level-lowered models), `IgusaScheme`/`IgusaFunctionFieldX1`,
`PlaceWidth`/`PlaceSpecialization`, `NeronModelInfra`, `JZeroNeronObjectAtP`,
`CerednikDrinfeld`, `CuspSpace`/cusp widths, and the mod-`ℓ` reduction/specialization
machinery. Note what is *not* in this list: the **q-adic place** presentation
(`Defs/QAdicPlace.lean`, `qIntegersBar : ValuationSubring F` at `:144`,
`qInftyPlaceBar` at `:316`) is ported, as are the arithmetic-Galois
(`arithmeticGalois`, `Defs/ArithmeticGalois.lean:75`), geometric base change
(`baseChangeEquiv`, `Defs/GeometricBaseChange.lean:167`, `geomAut :200`) and Frobenius
(`Frobenius/Defs.lean:237,295,303`) layers. What the port does **not** have is
`CurveModel`, the Deligne–Rapoport/Néron constructions, the automorphic field, or `X_H`.
That is exactly the large silo the frontier tooling flags.

One subtlety worth recording, because it changes what "the port has a modular curve"
means: the port has no *named* `IsCurveOver` instance for `modularFunctionFieldBar`.
Its only `IsCurveOver` on a modular field is a local `haveI`
(`ModularCurve/Frobenius/QExpModL.lean:553`) discharged from
`exists_transcendental_finiteDimensional_qExpFunctionFieldC`
(`X1/FunctionField.lean:1128`) via the generic
`isCurveOver_of_transcendental_of_perfectField`
(`AlgebraicCurve/IsCurveOver/Transcendental.lean:82`). The named instances
`isCurveOver_modularFunctionFieldBar` and
`functionFieldRiemannRoch_modularFunctionFieldBar` are **pin-only**. In the port, the
curve axiom is instead obtained where it is needed from principal divisors:
`hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull` and
`hasPrincipalDivisors_modularFunctionFieldBar_unconditional`
(`ModularCurve/PrincipalDivisors/ModularCurveBar.lean:63,82`).

### 2.4 The analytic track, and the field that is *not* bridged

Two analytic-side tracks exist:

* the port's `ModularCurve/Analytic/*`, which lives on the q-expansion side:
  `FrickeInvariance.lean` proves that the analytic modular unit series `Δ/Δ(q^p)`
  really lies in the modular function field
  (`modularUnitSeries_mem_modularFunctionField`, `:335`), i.e. the analytic object is
  recognized as a P2 element — a genuine P4 → P2 bridge;
* the pin's `automorphicField Γ ⊂ FractionRing holRing`
  (`Definitions/Def_ModularCurve_AutomorphicField.lean:150`), a *second* modular-curve
  function field built from holomorphic functions on `ℍ`, carrying its own
  `IsCurveOver ℂ` instance and its own `ℍ → Place` dictionary. It is used for the
  Čerednik–Drinfeld level-lowering step and is **not bridged** to `qExpFunctionFieldC`
  anywhere in the pin ([flt-function-field-theory-and-mathlib.md](flt-function-field-theory-and-mathlib.md) §7.4).
  The port's `Reserve/ModularCurve/Analytic/LevelTauBridge.lean` is the beginning of
  the lattice/τ side (`lat τ := span ℤ {1,τ}`, `:41`).

**Theory stack for modular curves.** P4 (Laurent/PowerSeries) → P2 (`IntermediateField`,
`IsCurveOver`, `Place`, `Divisor`, `Pic0`, `Correspondence`) → P3 (`CurveModel` built on
mathlib `Scheme` + `IsIntegral` + `SmoothOfRelativeDimension 1` + `ValuativeCriterion`,
via `TwoChartIntegralModel`). Mathlib contributes the scheme/valuation vocabulary and
`Scheme.functionField`; *everything* modular is FLT's. This is the opposite seam from
elliptic curves, where mathlib owns the bottom and FLT owns the top.

## 3. Modular forms

### 3.1 P4 — mathlib's analytic form and its q-expansion

The base is mathlib and it is genuinely the *analytic* presentation:

| object | kind | where |
|---|---|---|
| `SlashInvariantForm Γ k` | structure | mathlib `NumberTheory/ModularForms/SlashInvariantForms.lean:34` |
| `ModularForm Γ k` | structure, extends the above | mathlib `ModularForms/Basic.lean:74` |
| `CuspForm Γ k` | structure, extends the above | mathlib `ModularForms/Basic.lean:82` |
| `ModularFormClass` / `CuspFormClass` | classes | mathlib `Basic.lean:92,100` |
| `CongruenceSubgroup.Gamma0/Gamma1` | defs | mathlib `CongruenceSubgroups.lean:79,131` |
| `qExpansion : (ℍ → ℂ) → PowerSeries ℂ` | def | mathlib `ModularForms/QExpansion.lean:171` |
| `UpperHalfPlane` | type | mathlib `Analysis/Complex/UpperHalfPlane/Basic.lean` |

Mathlib stops there: no Hecke operators, no Laurent-valued q-expansion, no
order-at-cusp API, **no q-expansion principle**. FLT supplies the rest on the same
carrier. `qCoeff f n := (qExpansion 1 f).coeff n`
(`lean/FLTForHuman/ModularForms/HeckeQCoeff.lean:70`) is the working handle, and the
q-expansion principle and Sturm bound are ported:
`coeff_eq_zero_of_hasSum_of_slash_invariant`
(`ModularForms/QExpansionPrinciple.lean:223`),
`eq_zero_of_qExpansion_coeff_eq_zero` and `sturm_bound_Gamma0`
(`ModularForms/SturmBound.lean:336,230`).

### 3.2 P2 — modular functions, and why weight-*k* forms are not function-field elements

Weight **0** is the case where the two presentations literally coincide: an
`SL₂(ℤ)`-invariant function on `ℍ` is a function on `X(1)`, hence an element of the
function field. The port's `ModularForms/WeightOne/LevelField.lean` builds the level-`N`
version of that ring: `j : ℍ → ℂ` (`:74`), `levelGen N := insert j (range (frickeF N ·))`
(`:302`), `levelRing N ⊂ (ℍ → ℂ)` (`:304`), and
`levelField N := FractionRing levelRing` (`:445`). The bridging lemma is

* `mem_adjoin_jq_of_hasSum_of_slash_invariant` (`ModularForms/Hauptmodul.lean:452`) —
  an `SL₂(ℤ)`-invariant `F : ℍ → ℂ` whose Laurent series `f` sums to it lies in
  `ℚ[jq]`, i.e. the analytic weight-0 object *is* a function-field element;

plus its level-`ℓ` analogue `mem_adjoin_jq_of_phiGenDescends`
(`ModularForms/PhiGenDescends.lean:345`) and the algebraic/analytic dictionary
`JqAnalyticModel.hasSum_jq_qParam` (`:581`),
`qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` (`:335`) — the analytic `j`,
`Δ`, `E₄` equal the power series attached to `jq`, `jNum`, `eisenstein4`.

For weight `k > 0` there is **no** such collapse, and it is worth being explicit about
it: a weight-`k` form is a section of a line bundle, not a function, so the algebraic
handles are instead

* its **q-expansion** (P4, below), which is a plain power series and the object the
  Hecke algebra actually acts on;
* its **integral structure** — `intLattice N k` and `HasIntegralStructure`
  (`Defs/IntegralStructure.lean:25,30`), and for weight one the bundled
  `IntegralWeightOneForm` (§3.4);
* the **Katz section** presentation (P3, pin-only).

So "modular form" splits cleanly: weight 0 → function field, weight `k` → q-expansion
plus lattice/section data. Any argument that needs to move a positive-weight form into
a function field is really moving its q-expansion or its divisor, not the form.

### 3.3 P5 — Hecke algebra, eigenforms, Nebentypus

The Hecke structure lives on top of the analytic form and is entirely FLT's:

* surface operators `heckeU`/`heckeT` (`Defs/HeckeOperator.lean:136,139`), bundled as
  linear maps (`HeckeOperatorForms.lean:52,68`);
* `heckeAlgebra : Subalgebra ℤ (Module.End ℂ (CuspForm (Γ₀ N) k))`
  (`HeckeAlgebra.lean:40`) generated by `heckeGenerators` (`:35`), with `T`/`U` (`:100,104`);
* finiteness/integrality: `HeckeFiniteAlgebra.lean`, `HeckeLattice.lean`
  (`intLattice_fg`, `intLattice_free_and_finite`), `Defs/IntegralStructure.lean`
  (`intLattice N k`, `HasIntegralStructure N k`, `:25,30`);
* eigenforms: `IsNormalizedEigenform` (`Defs/Eigenform.lean:29`), with the equivalence
  of the abstract eigenvalue condition and the q-coefficient recursion
  `IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul`
  (`HeckeEigenform.lean:375`);
* Nebentypus/diamond operators: `HasNebentypus`/`IsEigenformWith`/`IsPrimitiveForm`
  (`Defs/PrimitiveFormGamma1.lean:23,29,48`), `GammaH` (`Defs/GammaH.lean:76`),
  `Level/Diamond.lean`.

There is also a purely formal Hecke action on power series, used to feed the algebraic
side: `PowerSeries.heckeU/heckeV/heckeT`
(`Defs/FormalHeckeOperators.lean:42,52,68`) and the Laurent version
(`ModularCurve/Defs/LaurentSeriesHecke.lean:54,103,123`), with
`LaurentSeriesHecke.heckeU_ofPowerSeries` (`:72`) tying it back.

### 3.4 The weight-one and cohomological presentations

The Deligne–Serre weight-one argument uses two further presentations:

* **P4 lattice.** `PeriodPair` is mathlib's
  (`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean:60`); the port's
  `WeightOne/Defs/PeriodPair.lean:29` fixes the standard pair `(τ,1)`, and
  `WeightOne/Defs/PTorsion.lean` builds the torsion values `wpTorsion` (`:61`),
  `wpNorm` (`:91`), `frickeH` (`:131`) out of mathlib's Weierstrass ℘. This is the
  complex-uniformization route to weight-one forms.
* **P2 integral structure.** `IntegralWeightOneForm`
  (`WeightOne/IntegralWeightOneForm.lean:74`) bundles a weight-one form with an
  *integral* q-expansion: fields `form : ModularForm (Γ₁ M) 1` and
  `series : PowerSeries ℤ`. The rationality/integrality transfers are
  `WeightOne/Gamma0Integral.lean` (`IsIntegralQExp :98`, headlines at `:1320,1905,2339`),
  and `WeightOne/Gamma1Basis.lean`/`Gamma1IntegralBasis.lean` give the basis by
  `E₄^a E₆^b · fricke`.
* **Cohomology.** `BinaryForm K n` (`EichlerShimura/BinaryForm.lean:80`) is the
  representation space; `coeffH1par ρ` (`CoeffCohomology.lean:163`) is parabolic
  group cohomology `H¹`; `periodOf` (`PeriodOf.lean:72`), `periodLatticeOf` (`:81`) and
  `periodMap` (`PeriodPrimitive.lean:129`, `PeriodMap.lean:968`) are the period
  presentation. The pin's Hecke-stability half of the period lattice is explicitly
  **not ported**.
* **Eisenstein.** `eisensteinG` (`ModularForms/EisensteinSeries.lean:60`) is re-derived
  over the full congruence class rather than from mathlib's level-one
  `eisensteinSeries`, because they differ already at level 1; the coefficients come from
  `weierstrassZeta` (`Eisenstein/WeierstrassZeta.lean:13`) and
  `qExpansion_eisensteinG_coeff` (`EisensteinSeries.lean:658`).

*Not ported:* the Katz/line-bundle presentation `KatzModularForm R k`
(`Definitions/Def_ModularForm_KatzLevelOne.lean:9`) — a rule assigning to each
`(A, WeierstrassCurve A, IsUnit Δ)` an element of `A`, i.e. a section of `ω^k` over the
moduli stack; `Def_ModularCurve_OmegaOf`, `KatzLevelPYoneda`, the Petersson API, and the
whole adelic/automorphic block (`Def_AutomorphicForm_*`, 106 files) and
Čerednik–Drinfeld layer.

**Theory stack for modular forms.** P4 is mathlib `SlashInvariantForm`/`ModularForm`/
`CuspForm` + `UpperHalfPlane` + `PowerSeries`/`LaurentSeries` + `PeriodPair`/Weierstrass
℘. P2 is FLT's `IntermediateField ℚ (LaurentSeries ℚ)` plus the `AlgebraicCurve`
place/divisor layer. P5 is FLT's Hecke algebra over `ℤ`, its finiteness, and the
eigenform/Nebentypus API. The bridges are FLT's too: q-expansion principle, Sturm bound,
`qCoeff`, `mem_adjoin_jq_of_hasSum_of_slash_invariant`.

## 4. The theory stack, side by side

Reading the table: "mathlib" means supplied unchanged, "port" means FLT-developed and
present in `lean/FLTForHuman`, "pin-only" means developed but not yet ported.

| presentation | elliptic curve | modular curve | modular form |
|---|---|---|---|
| **P0/P1 concrete** | mathlib `WeierstrassCurve`, `Affine/Projective/Jacobian.Point`; port `FreyPackage`, `Elliptic/Universal` | port `ProjectiveLine` (the `j`-line) | — |
| **P2 function field** | mathlib `Affine.FunctionField`; port `Place`/`Divisor`/`Pic0`; pin-only `GenusOnePlaceGate` (`E≅Pic⁰`) | port `modularFunctionField`/`Full`/`Bar`, `qExpFunctionFieldC` (`X₀`), `x1FunctionFieldC`, `jq`, cusps, `JZero`, `Correspondence`; `X_H` pin-only | port `levelRing`/`levelField`, `jq`-membership |
| **P3 scheme/model** | pin-only `WeierstrassCurve.ProjModel`, `NeronModelInfra` | pin-only `CurveModel`, `TwoChartIntegralModel`, `DRModelPackage`, `CharPModel`, `XHDRModelAtP`, `IgusaScheme` | pin-only `KatzModularForm` (section of `ω^k`) |
| **P4 local series** | mathlib `PowerSeries`/`LaurentSeries`, `PeriodPair` (complex uniformization); port ω/EDS; pin-only `TateCurve`, `FormalGroup` | port `QAdicPlace`/cusps, `Analytic/CuspBookkeeping`, `FrickeInvariance`, `ModularUnit`; `X_H` pin-only | mathlib `qExpansion`; port `qCoeff`, q-expansion principle, Sturm, `PTorsion` |
| **P5 arithmetic** | pin-only Tate module, Galois rep, reduction maps; port `reductionMod`/`IsModular` | port `heckeOperatorBar`, `heckeModuleBar`, `cuspidalClass`, `qExpFrobeniusModL`; pin-only Néron/specialization | port Hecke algebra/lattice/eigenforms/Nebentypus; pin-only Petersson |

## 5. The bridges that carry the weight

These are the lemmas that move an object between presentations; they are where the
subjects actually connect, so they are the best entry points for a reader.

Elliptic curves:

* `Affine.Point.toClass` (mathlib `Affine/Point.lean:752`) — point to ideal class;
* `GenusOnePlaceGate.pointEquivPlace` / `divisorSum` (pin, `Def_WeierstrassCurve_GenusOnePic0.lean:29,46`)
  — affine point ⇄ degree-one place, `E(K) ≅ Pic⁰` (unported);
* `Projective.Point.toAffineAddEquiv` / `Jacobian.Point.toAffineAddEquiv` / `fromAffine`
  (mathlib) — the three point models;
* `smul_eq_zero_iff_evalEval_ψ` (port `Elliptic/Bridge.lean:53`) — torsion ⇄ division
  polynomial;
* `zsmul_eq_smulEval` (port `Elliptic/JacobianMulFormula.lean:258`) — universal point ⇄
  coordinates.

Modular curves:

* `ord_qInftyPlaceBar` / `ord_cuspInftyBar` (port `Analytic/CuspBookkeeping.lean:78,108`)
  — Laurent series order ⇄ place order at a cusp, with
  `ord_cuspInftyBar_coeffEmb_qExpand` (`:120`, value `−d`) and the Fricke swap
  `frickeInvolutionBar_coeffEmb_qExpand` (`:127`) exchanging `qExpand a jq ↔ qExpand b jq`
  for `a·b = N`;
* `isCusp_iff_ord_neg` / `eq_cuspInftyBar_or_eq_cuspZeroBar` (port
  `Analytic/CuspBookkeeping.lean:177`, `Analytic/CuspDichotomy.lean:252`) — the cusp
  predicate in valuation language (`isCusp_iff`, `Defs/QAdicPlace.lean:375`), and the
  fact that `X₀(ℓ)` has exactly the two cusps;
* `modularUnitSeries_mem_modularFunctionField` (port `Analytic/FrickeInvariance.lean:335`)
  — analytic modular unit ⇄ function-field element, with
  `isIntegral_adjoin_jq_modularUnitSeries` (`:382`) and the q-expansion side
  `hasSum_modularUnitSeries_qParam` (`Analytic/ModularUnitQExpansion.lean:440`);
* `hasPrincipalDivisors_modularFunctionFieldBar_unconditional` (port
  `PrincipalDivisors/ModularCurveBar.lean:82`) — the q-expansion generators supply the
  principal-divisor half of the curve axiom;
* `baseChangeEquiv` (port `Defs/GeometricBaseChange.lean:167`) — tensor product of
  function fields ⇄ coefficientwise Laurent base change, with `arithmeticGalois` and
  `coe_arithmeticGalois_smul` (`Defs/ArithmeticGalois.lean:75,99`) the Galois action;
* `qExpFunctionFieldC ℚ (Gamma0 M) = modularFunctionFieldFull M` (pin `Thm…:13`) — the
  Deligne–Rapoport ⇄ `X_H` dictionary;
* `CurveModel.placeEquiv` / `pointEquivPlace` (pin `CurveModel.lean:67,73`) — scheme
  closed points ⇄ places (unported).

Modular forms:

* `qCoeff` = `(qExpansion 1 f).coeff` (port `HeckeQCoeff.lean:70`) — analytic form ⇄
  q-series;
* `IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul` (port `HeckeEigenform.lean:375`)
  — Hecke eigenvalue ⇄ coefficient recursion;
* `mem_adjoin_jq_of_hasSum_of_slash_invariant` (port `Hauptmodul.lean:452`) — invariant
  q-series ⇄ polynomial in `jq`;
* `hasSum_jq_qParam` / `qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` (port
  `JqAnalyticModel.lean:581,335`) — analytic `j`/`Δ` ⇄ algebraic `jq`/`jNum`;
* `weierstrassZeta` → `eisensteinG` → `qExpansion_eisensteinG_coeff` (port
  `Eisenstein/WeierstrassZeta.lean:13`, `EisensteinSeries.lean:60,658`) — lattice ζ ⇄
  Eisenstein q-series;
* `cuspidalDivisor` → `cuspidalClass : JZero N` (port `CuspidalClass.lean:40,63`) —
  cusp divisor ⇄ Jacobian class.

## 6. What this implies for the port

1. **The elliptic-curve bottom is a mathlib-first success and should stay that way.**
   P0/P1 are mathlib; the port's own `Elliptic/*` is only the genuine gap (ω/EDS,
   universal curve, torsion). New elliptic-curve work should default to mathlib and
   port only P2/P4 additions.

2. **The modular curve's centre of gravity is P4 → P2, not P3.** The port's landed
   value is the q-expansion function field, its place dictionary, the Hecke
   correspondences and the Jacobian. The expensive unported silo is the scheme/moduli
   side (`CurveModel`, Deligne–Rapoport, Néron, Čerednik–Drinfeld) together with the
   unbridged `automorphicField`. That is where a large porting decision lives.

3. **Modular forms are already a two-way bridge; protect the bridges.** The most
   valuable ported lemmas are not the big files but the cross-presentation identities
   (`qCoeff`, q-expansion principle, Sturm, `mem_adjoin_jq_…`, the `JqAnalyticModel`
   equalities). These are what turn "a function on `ℍ`" into a usable algebraic object,
   and they are exactly what the Deligne–Serre route consumes.

4. **The remaining presentations are arithmetic, not analytic.** Katz/`ω^k`,
   mod-`p` forms, Tate module, formal group, Petersson: these are the natural next
   subjects if the port goes further into the modularity-lifting / weight-one end.

5. **Two objects are deliberately split and should be flagged whenever cited.**
   `Pic0` of `modularFunctionFieldBar` *is* `J₀(N)` here (no variety), and
   `automorphicField` is a second, unbridged model of the modular curve. A reader who
   assumes a scheme-theoretic `X₀(N)` or a single function field will misread both.

## 7. Index of the load-bearing objects

Port paths are relative to this repository; pin paths to
`anthropics/fermats-last-theorem@aa2d8b3`; mathlib paths to `v4.34.0`.

| object | stratum | provenance | ported? |
|---|---|---|---|
| `WeierstrassCurve`, `IsElliptic`, `VariableChange` | P0 | mathlib | yes |
| `FreyPackage`, `freyCurveInt` | P0 | port `WeierstrassCurve/Defs/FreyPackage.lean:22,88` | yes |
| `Affine.Point`, `Projective.Point`, `Jacobian.Point` | P1 | mathlib | yes |
| `Elliptic.Universal.curve`, `affinePoint`, `jacobianPoint` | P1 | port `Elliptic/Universal.lean:61,145,152` | yes |
| `Place`, `Divisor`, `Pic0`, `IsCurveOver` | P2 | port `AlgebraicCurve/Defs/*` | yes |
| `GenusOnePlaceGate`, `placeOfPoint`, `divisorSum` | P2 | pin `Def_WeierstrassCurve_GenusOnePic0.lean:18,29,46` | no |
| `WeierstrassCurve.ProjModel`, `RelativeGroupLaw` | P3 | pin `Def_WeierstrassCurve_ProjModel.lean:67,301` | no |
| `TateCurve.curve`, `pointX`, `pointY`, `tateTorsionEquiv` | P4 | pin `Def_TateCurve_QSeries.lean:185`, `PointSeries.lean:179,181` | no |
| `CurveModel`, `placeEquiv`, `pointEquivPlace` | P3 | pin `Def_AlgebraicCurve_CurveModel.lean:23,67,73` | no |
| `modularFunctionField`, `modularFunctionFieldFull` | P2 | port `ModularCurve/Defs/Fields.lean:42,137` | yes |
| `qExpFunctionFieldC` (= `X₀`), `x1FunctionFieldC` (= `X₁`) | P2 | port `ModularCurve/JqIntegralRatios.lean:92`, `X1/Defs.lean:75` | yes |
| `xHFunctionFieldC`, `xHFunctionFieldBar` (= `X_H`) | P2 | pin `Def_ModularCurve_XH.lean:76,123` | no |
| `jq`, `jqN`, `TS`, `qTwist` | P2 | port `ModularCurve/Defs/Jq.lean:110`, `Defs/TS.lean:39`, `Defs/Twist.lean:54` | yes |
| `ModularPolynomialData` (`Φ_N`) | P2 | port `ModularCurve/Defs/Polynomial.lean:31` | yes |
| `JZero`, `JOne`, `cuspidalClass` | P1/P2 | port `Defs/ArithmeticGalois.lean:114`, `X1/Defs.lean:133`, `Defs/CuspidalClass.lean:63` | yes |
| `cuspInfty`, `cuspInftyBar`, `IsCusp`, `frickeInvolutionBar` | P1/P2 | port `Defs/QAdicPlace.lean:351,372`, `Defs/AtkinLehner.lean:111`, `Defs/CuspidalClass.lean:26` | yes |
| `qIntegersBar`, `qInftyPlaceBar` | P4 | port `Defs/QAdicPlace.lean:144,316` | yes |
| `heckeOperatorBar`, `HeckeAlg`, `heckeModuleBar` | P5 | port `Defs/HeckeModule.lean:35,71,122` | yes |
| `correspondence` (generic Hecke shape) | P2 | port `AlgebraicCurve/Defs/Correspondence.lean:242` | yes |
| `ord_qInftyPlaceBar`, `ord_cuspInftyBar` | P4→P2 | port `Analytic/CuspBookkeeping.lean:78,108` | yes |
| `modularUnitSeries`, `modularUnitSeries_mem_modularFunctionField` | P4→P2 | port `Defs/ModularUnit.lean:141`, `Analytic/FrickeInvariance.lean:335` | yes |
| `CurveModel`-based DR/CharP/XHDR/Igusa/Néron family | P3 | pin `Def_ModularCurve_*`, `NeronModelInfra`, `CerednikDrinfeld` | no |
| `automorphicField` | P2 | pin `Def_ModularCurve_AutomorphicField.lean:150` | no |
| `SlashInvariantForm`, `ModularForm`, `CuspForm`, `qExpansion` | P4 | mathlib | yes |
| `qCoeff`, q-expansion principle, `sturm_bound_Gamma0` | P4 | port `HeckeQCoeff.lean:70`, `QExpansionPrinciple.lean:223`, `SturmBound.lean:230` | yes |
| `levelRing`, `levelField`, `LevelGens` | P2 | port `WeightOne/LevelField.lean:304,445,732` | yes |
| `heckeAlgebra`, `intLattice`, `IsNormalizedEigenform` | P5 | port `HeckeAlgebra.lean:40`, `Defs/IntegralStructure.lean:25`, `Defs/Eigenform.lean:29` | yes |
| `PeriodPair`, `wpTorsion`, `wpNorm` | P4 | mathlib `Weierstrass.lean:60`; port `PTorsion.lean:61,91` | yes |
| `IntegralWeightOneForm` | P2 | port `WeightOne/IntegralWeightOneForm.lean:74` | yes |
| `BinaryForm`, `coeffH1par`, `periodOf`, `periodMap` | P5 | port `EichlerShimura/*` | yes |
| `eisensteinG`, `weierstrassZeta` | P4 | port `EisensteinSeries.lean:60`, `Eisenstein/WeierstrassZeta.lean:13` | yes |
| `KatzModularForm` | P3 | pin `Def_ModularForm_KatzLevelOne.lean:9` | no |

## 8. Reproduce

Every claim above is a source read, not a graph statistic. The counts quoted in the
companion scouts (frontier size, per-cluster nodes/lines) come from the untracked
`tools/deps` front end — `frontier.py --selfcheck` for the frontier, `frontier.py
--one-hop --sort-by silo` for the big unported clusters — and are reproduced there, not
here. Two checks worth re-running when the port moves:

* the place/function-field seam: `Place` and `Divisor` still live only in
  `lean/FLTForHuman/AlgebraicCurve/Defs/`, and `CurveModel` is still absent from the port
  (`grep -rn "structure CurveModel" lean/`);
* the q-expansion bridges: `qCoeff`, `sturm_bound_Gamma0`,
  `mem_adjoin_jq_of_hasSum_of_slash_invariant` still exist under
  `lean/FLTForHuman/ModularForms/`, and `qCoeff` is still the handle the Deligne–Serre
  assembly works through (`lean/FLTForHuman/DeligneSerre/CoefficientRing.lean`).
