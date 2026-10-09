# The Eichler–Shimura package — port scout

**Status (2026-09-27; period-map milestone recorded 2026-09-28).** A living port
scout for the **full Eichler–Shimura isomorphism**. §1 fixes the driver, §2 is
the pin's inventory and consumer map, §3 the baseline effort, §4 what the port
has already landed, §5 the gap, §6 the port order, and Appendix C the core's
definition layer and the pin's two cohomologies. Everything is measured against
the FLT pin `aa2d8b3` with
`tools/deps` (docs-site graph closure) plus source greps of the pin's `S_`/`Thm_`
files; the port's mathlib is `v4.34.0`.

**Route B is no longer on the path.** Its blob proves the weight-2 slice of the
same map plus a finiteness statement C′ already gives; it adds no coverage, and
it is recorded as a `lean/Reserve/` candidate (§1.3).

Companions: [flt-non-frey-segments.md](flt-non-frey-segments.md) §8–§8.1,
[route-c-prime-scout.md](route-c-prime-scout.md),
[../math/017-eichler-shimura-isomorphism.md](../math/017-eichler-shimura-isomorphism.md)
(the mathematics — the classical isomorphism and its ingredients),
[../math/015-weight-two-hecke-periods.md](../math/015-weight-two-hecke-periods.md)
(route B, now Reserve),
[../math/016-mod-p-weight-filtration.md](../math/016-mod-p-weight-filtration.md)
(the mod-$`p`$ weight filtration, retained as background).

## 0. Terminology

The words "Eichler–Shimura", "E-S" and "route A" have been used for three
different objects; the measurements are reproduced here.

| object | what it is | size |
|---|---|---|
| **route A** | the *integral-structure* route: the pin's proof of `CuspForm.hasIntegralStructure_of_two_le` (and `moduleFinite_heckeAlgebra` above it) | 657 nodes / 263,720 lines, ~528 of them modular-curve / elliptic geometry |
| **the E-S isomorphism** | the period map $`S_k \to H^1_{par}(\Gamma_0, \mathrm{Sym}^{k-2})`$ and its two-piece decomposition; the mathematical content below | the driver (§1) |
| **the E-S cohomological layer** | the `HeckeEis` nodes carrying the content on the cohomology side: `eichlerShimuraMap`, `coeffH1par`, the conjugate half, the integral basis, the dimension bound. The driver is **stated over** this layer, so it is the object side of the isomorphism — not disposable "packaging" | 33 nodes / 10,789 `S_` lines (§2.1) |

Route A is not an E-S cone, and the E-S isomorphism is not the cohomological
layer; separating them changes the payoff accounting. C′ replaces route A's
*proof* for **4 nodes / 800 lines**
([route-c-prime-scout.md](route-c-prime-scout.md) §4 addendum).

**On the name `HeckeEis`.** It is a Lean namespace in the pin; its "Eis" is the
pin's shorthand for *Eichler–Shimura* (the definition module is titled "Eichler
integrals and the Eichler–Shimura map to parabolic cohomology"). It is ambiguous
with *Eisenstein* and mixes kept and removed material, so it is used here only as
a literal Lean identifier.

**Is a replaced route still needed?** That is a separate, testable question — the
pin's cone can carry a route's nodes without the consumer using that route's proof.
§8 gives the two commands that decide it, with the D-S column's route-A replacement
as the worked case.

## 1. The driver

### 1.1 The statement

The driver is the classical **Eichler–Shimura isomorphism** in the form the
endgame needs. The pin's packaged form is
`HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime (N) [NeZero N] (n)`:

```lean
∃ (ES    : CuspForm (Γ₀ N) ((n:ℤ)+2) →ₗ[ℂ] coeffH1par (binaryFormRepSL ℂ n ∘ Γ₀.subtype))
  (ESbar : CuspForm (Γ₀ N) ((n:ℤ)+2) →ₛₗ[starRingEnd ℂ] coeffH1par (binaryFormRepSL ℂ n ∘ Γ₀.subtype)),
  Function.Injective ES ∧ Function.Injective ESbar ∧
  IsCompl (LinearMap.range ES) (LinearMap.range ESbar) ∧
  (∀ ℓ prime, ℓ ∤ N, ∀ T Hecke on coeffH1par, (∀ f, T (ES f) = ES (heckeTLin f)) ∧
                                             (∀ f, T (ESbar f) = ESbar (heckeTLin f))) ∧
  (∀ ℓ prime, ℓ ∣ N, ∀ T Hecke on coeffH1par, (∀ f, T (ES f) = ES (heckeULin f)) ∧
                                             (∀ f, T (ESbar f) = ESbar (heckeULin f)))
```

i.e., in the mathematics of
[017](../math/017-eichler-shimura-isomorphism.md),

$$H^1_{par}(\Gamma_0(N), \mathrm{Sym}^{k-2}) \\;\cong\\; S_k(\Gamma_0(N)) \oplus \overline{S_k(\Gamma_0(N))}$$

as Hecke modules, the isomorphism being the period map and its complex conjugate.
A port-facing statement would name it once (`eichlerShimura_isomorphism`) rather
than bundle it in an existential, and would define the period map separately.

### 1.2 Why this driver

* **It is the classical statement, with math content.** Eichler (1957) and
  Shimura (1959); the pin's generated titles call it "Eichler–Shimura
  decomposition of parabolic cohomology". It is a landmark of the theory even
  though it is not one of the pin's 49 route landmarks
  (`PROOF-PATH.md` names no E-S step).
* **It is uniform in the weight.** No form-side weight descent is needed, which
  is what makes it a single driver rather than a family.
* **It is exactly the source of the endgame's two E-S consumers.** Interfaces 1
  (level raising, the mod-$`p`$ eigenclass) and 4 (char-3 weight $`\le 4`$, the
  classification of `H¹` eigensystems) are the only interfaces whose closure
  meets the cohomological layer at all (§2.2). Interface 1 needs the period map,
  the integral lattice and the eigenclass; interface 4 needs the surjectivity /
  Eisenstein half.
* **It strictly contains route B.** Route B is the $`n = 0`$ slice, where the
  quotient and the anti-holomorphic half both vanish.

### 1.3 Route B is retired to `lean/Reserve/`

Route B's 4,308-line blob (`S_CuspForm_moduleFinite_heckeAlgebra_two.lean`) is
self-contained (graph closure 1) and pleasant, but it proves:

* the weight-2 period map and its injectivity — the $`n = 0`$ slice of the
  driver, so no coverage the driver does not give; and
* a finiteness statement (`moduleFinite_heckeAlgebra_two`) that C′'s integral
  structure already implies in every weight
  ([../math/015-weight-two-hecke-periods.md](../math/015-weight-two-hecke-periods.md)
  role-correction).

So it contributes nothing to the critical path. Its value is pedagogical: a
self-contained worked instance of the period construction. That is precisely the
`lean/Reserve/` convention (a verified alternative route kept out of the
critical-path library), and it is recorded there in
[../lean/Reserve/README.md](../lean/Reserve/README.md).

## 2. The pin's package: inventory and consumers

### 2.1 The 33-node cohomological layer `R`

`R` is the set matched by the patterns `eichlerShimuraMap` and `coeffH1par`:
**33 nodes / 10,789 `S_` lines** in the `HeckeEis` namespace. It is the
cohomology side of the isomorphism — the carrier `ES` lands in plus its packaged
assembly — grouped by role below; over
$`\Gamma_0(N)`$, $`V_n =`$ `BinaryForm ℂ n`, representation `binaryFormRepSL`,
Hecke `binaryFormAlphaAdj`, weight $`k = n+2`$:

| group | nodes | lines | content |
|---|---:|---:|---|
| 1. the period map | 4 | 394 | `eichlerShimuraMap` additive, ℂ-homogeneous, injective |
| 2. the two halves | 5 | 2,000 | conjugate-linear involution, complementarity, packaged isomorphism |
| 3. Hecke equivariance | 4 | 1,742 | existence of the cohomological $`T_\ell`$, $`U_\ell`$, and the square |
| 4. coefficient change / functoriality | 3 | 1,142 | base change, equivariant retractions, Shapiro/projLine |
| 5. integral structure | 9 | 3,521 | torsion-freeness, integral basis, base change, denominators |
| 6. dimension theory | 4 | 1,180 | Euler-characteristic / genus bounds |
| 7. mod-$`p`$ eigenclass and boundary | 4 | 810 | integral eigenclass mod $`p`$; the Eisenstein boundary |

The full list with the pin's English titles is Appendix A. Three nodes are
**interface-facing** — the only members of `R` whose consumers outside `R` are an
endgame interface (all three feed interface 1) rather than another member of `R`,
route A / `finite_int_heckeAlgebra`, an analytic node, or the retained re-proved
node `HeckeEis.exists_modularForm_heckeTLin_eq_smul_of_isEigensystemH1`:

* `exists_coeffH1par_projLineRepSL_equiv_parabolicHoms` (710) → interface 1;
* `exists_coeffH1par_map_of_equivariant_retraction` (174) → interface 1;
* `exists_coeffH1par_binaryFormRepSL_eigenclass_of_ideal_heckeAlgebra_of_ne_two`
  (61) → interface 1.

### 2.2 The consumer map: only two interfaces touch `R`

Of the ten maximal interfaces
([flt-non-frey-segments.md](flt-non-frey-segments.md) §8, and `tools/deps`'
`INTERFACES`), only two have any of `R` in their closure. The other eight are either **C′-dissolved** (interfaces 5 and 6 fall
from 25 `R`-nodes to **0** once `hasIntegralStructure_of_two_le` is supplied by
C′) or never touch `R` (2, 3, 7, 8, 9, 10).

| interface | `R`-closure | endgame role | needs the full isomorphism? |
|---|---:|---|---|
| 1. `WeierstrassCurve.exists_ideal_heckeAlgebra_mul_two_…` | 20 / 6,369 | level raising: a nonzero mod-$`p`$ eigenclass | **no** |
| 4. `WeierstrassCurve.exists_ideal_heckeAlgebra_three_weight_le_four_…` | 25 / 8,648 | char-3, weight $`\le 4`$: classify `H¹` eigensystems | **yes**, on its current branch |

**Interface 1 wants existence, not surjectivity.** Its `R`-closure is the period
map (group 1), the $`T_\ell`$-equivariance (part of group 3), the integral
structure (part of group 5), the mod-$`p`$ eigenclass (group 7), and the
Shapiro/projLine and retraction carrier maps (group 4). Injection plus an
integral lattice is enough to produce the eigenclass.

**Interface 4 wants the full isomorphism.** Its path reaches the packaged
isomorphism through `HeckeEis.exists_modularForm_heckeTLin_eq_smul_of_isEigensystemH1`
("eigensystems in `H¹(Γ₀(N), Symⁿ)` arise from weight `n+2` forms") and the
boundary node. That is the surjectivity / Eisenstein half: every `H¹` eigensystem
comes from a form, which needs $`H^1_{par}`$ to be exactly the cuspidal part —
complementarity and, through it, the dimension theory. But the same input lemma
also cites the **intrinsic** mod-$`p`$ core
`ModPForms.exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen`, which sits on
the kept analytic core and not on `R`; so interface 4 has a routing choice, and
the full isomorphism is on only one of the two branches.

### 2.3 The 12-node analytic core

The driver's period map rests on the 12-node analytic set (Appendix B):
the Eichler-integral existence input, the transport/slash and difference-by-a-
constant lemmas, the iterated-$`\partial_1`$ identity, the boundedness-at-cusp
lemma, the Hecke-correspondence transport, the two algebraic bridge lemmas, and
the period Hecke-equivariance and injectivity statements. The full list with line
counts is Appendix B. Of the twelve, **ten** are in the driver's closure; the two
not needed are `coeffH1Mk_cocycle_heckeTLin_modularForm` and
`modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero`, which belong to the
target-lemma form of the statement rather than to the isomorphism. Nine of the
ten have since landed (Appendix C §C.3).

## 3. Baseline effort: the full isomorphism

### 3.1 The closure

The closure of `exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime` in
the pin is **645 nodes / 260,938 lines**. That headline is mostly geometry: the
dimension theory of group 6 reaches `ModularCurve.genusFormula`, `nuTwo`,
`nuThree`, `cuspCount`, the Riemann–Roch / `AlgebraicCurve` cone and the
`JZero`/`Tate` arithmetic. By namespace:

| namespace | nodes | lines | relation to the driver |
|---|---:|---:|---|
| `WeierstrassCurve` | 100 | 91,063 | shared endgame geometry (needed regardless) |
| `AlgebraicCurve` | 162 | 69,010 | shared geometry |
| `ModularCurve` | 266 | 67,287 | shared geometry |
| `HeckeEis` | 49 | 12,003 | **E-S-specific** |
| `PeriodPair` | 9 | 9,836 | shared uniformisation |
| others | ~59 | ~11,739 | mathlib gaps, `CuspForm`/`ModularForm` |

So the port surface that is *E-S-specific* is the `HeckeEis` 49, not the 645.

### 3.2 The E-S-specific surface

| piece | pin `S_` lines | note |
|---|---:|---|
| cohomological layer, groups 1, 2, 3, 4, 6 (23 nodes) | 8,127 | the isomorphism proper |
| analytic core, 10 of 12 nodes | 1,388 | the period map's analysis |
| E-S dimension / representation helpers (16 nodes) | 2,488 | `exists_induced_binaryFormRepSL_top`, `le_finrank_fixed_*`, `exists_pairing_binaryForm_linePow`, `existsEichlerShimuraMapLinear`, … |
| definition modules (5) | 858 | `BinaryFormRep` 140, `Gamma0CoeffCohomology` 153, `Gamma0CoeffCohomologyEigen` 112, `HeckeEis_EichlerIntegral` 149, `Gamma0HeckeOperatorHom` 304 |
| external mathlib-absent lemmas (3) | 365 | star-convex antiderivative 150, boundedness-at-cusp 175, iterated `pderiv` 40 |
| `Thm_` statement files | ~250 | wrappers; a port states directly |

**Total: roughly 13,200 `S_` lines of E-S-specific Lean**, of which ~2,731 have
landed (the period-map milestone: §4, Appendix C §C.3). For comparison, route B's
self-contained blob is 4,308 lines; the driver is the same order (about
$`3\times`$) and strictly contains it.

The `R`-minus-driver remainder is the ten nodes the isomorphism does not use
(the eigenclass, the boundary, the projLine equivalence, the retraction, the
denominators); they are the optional mod-$`p`$ layer of §6.

### 3.3 The external mathlib-absent lemmas

Three theorem dependencies are outside the 12 and absent from mathlib `v4.34.0`:

| lemma | `S_` lines | content |
|---|---:|---|
| `Complex.exists_hasDerivAt_of_starConvex` | 150 | radial path integral differentiated under the integral sign |
| `UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic` | 175 | $`v' = u`$, $`u`$ bounded and periodic, $`v`$ periodic $`\Rightarrow`$ $`v`$ bounded at the cusp |
| `MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt` | 40 | pure `MvPolynomial` algebra |

They are the analysis/analysis-adjacent gap, and the port's first written layer
(landed; Appendix C §C.1).

### 3.4 The minimum cone: the period map and its injectivity

The first milestone is the general-weight period map and its injectivity — the
closure of `HeckeEis.eichlerShimuraMap_injective` (the structural `periodMap` in
the port):

| piece | nodes | `S_` lines |
|---|---:|---:|
| `HeckeEis` theorem nodes | 22 | 2,149 |
| definition modules (`Def_HeckeEis_BinaryFormRep`, `Def_Gamma0CoeffCohomology`, `Def_HeckeEis_EichlerIntegral`) | 3 | 442 |
| external theorem nodes | 5 | 610 |
| `Thm_` statement wrappers | — | ~200 |
| **total** | **27 + 3 defs** | **~3,400** |

The five external nodes are the whole mathlib gap:
`Complex.exists_hasDerivAt_of_starConvex` (150),
`UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic` (175),
`ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four` (135),
`UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty` (110) and
`MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt` (40). All five have
landed.

Two facts make the cone small:

* it uses only **three** definition modules — `Def_HeckeEis_BinaryFormRep`,
  `Def_Gamma0CoeffCohomology` and `Def_HeckeEis_EichlerIntegral`. It needs
  **neither** the Hecke correspondence (`Def_Gamma0HeckeOperatorHom`) **nor** the
  eigen/quotient module (`Def_Gamma0CoeffCohomologyEigen`), because injectivity
  contains no Hecke operator;
* the port's landed Hecke-form layer (`HeckeOperatorForms.lean`) is not used.

So the minimum cone is **~3,400 lines, of which ~2,731 have landed — smaller than
Route B's own 4,308-line blob**, and strictly stronger (it is the general
statement, of which Route B is the $`n = 0`$ specialisation). The E-S-specific
`HeckeEis` part is 22 nodes / 2,149 lines; the rest is definition and analysis
infrastructure the full driver needs anyway.

The difficulty was concentrated in the five externals — the star-convex
antiderivative, the Liouville-type boundedness at the cusp, the trace
classification and the iterated-`pderiv` algebra — plus the two large analytic
nodes `IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv` (305) and
`IsEichlerIntegral.slash` (191); all landed. The port plan is
[../lean/topics/eichlerShimura/TOPIC-period-map-injectivity.md](../lean/topics/eichlerShimura/TOPIC-period-map-injectivity.md),
now **COMPLETE** (build-green, `sorry`-free, checker-registered; record in
[../lean/logs/eichler-shimura-port.md](../lean/logs/eichler-shimura-port.md)).

**Why the full isomorphism is not "this cone plus surjectivity".** The full
statement is not "`ES` is bijective". `ES : S_k \to H^1_{par}` lands in a space
of dimension $`2\dim S_k`$, so `ES` is never surjective — it is injective onto
the *holomorphic* half. The bijective map is the doubled one

$$E : S_k \oplus \overline{S_k} \longrightarrow H^1_{par},
\qquad E(f, g) = ES(f) + \overline{ES}(g),$$

and both of its properties cost more than the minimum cone:

* $`E`$ **injective** needs, besides the two injectivities, the **disjointness**
  $`\mathrm{range}\,ES \cap \mathrm{range}\,\overline{ES} = 0`$ — the pin's
  1,325-line `range_eichlerShimuraMap_inf_range_conj_eq_bot`, where the
  positivity of the Petersson product hides (the Hodge–Riemann analogue);
* $`E`$ **surjective** (the **spanning**) is not proved by exhibiting preimages
  but by the dimension count `isCompl_range_eichlerShimuraMap_range_conj` draws
  from `finrank_coeffH1par_le_two_mul_dimFormula`, which is why the add-on
  reaches the modular-curve genus/cusp geometry.

On top of that the pin bundles the Hecke equivariance and the integral structure
into the same statement. Measured, the add-on over the minimum cone is **27
`HeckeEis` nodes / 9,854 lines** (conjugate half 332, disjointness 1,325,
dimension/spanning ~2,300, Hecke equivariance 1,549 + the correspondence, the
integral basis and base change, the assembly), plus the shared geometry the
dimension count reaches. "Surjectivity" is neither the size nor the shape of the
gap.

## 4. What has already landed

The port (`lean/FLTForHuman`) carries a large part of the *shared* layer the
driver needs, and — since the period-map milestone (2026-09-28) — the
map+injectivity share of the E-S-specific layer.

| landed (shared) | file | relevance to the driver |
|---|---|---|
| Hecke operators on forms `heckeTLin`/`heckeULin` | `ModularForms/HeckeOperatorForms.lean` (184) | the target of the Hecke-equivariance square |
| Hecke representatives on $`\mathbb{P}^1(\mathbb{F}_p)`$ | `ModularForms/Defs/HeckeRepresentatives.lean` | the coset/reindexing machinery |
| $`\Gamma_0(N)`$ index, $`\mathbb{P}^1(\mathbb{Z}/N)`$ count, Dedekind $`\psi`$ | `ModularCurve/Gamma0Index.lean` (773) | the dimension theory's index and cusp counts |
| Sturm bound, `finiteDimensional_Gamma0` | `ModularForms/SturmBound.lean` (451) | finite-dimensionality of cusp forms |
| C′ integral structure | `ModularForms/WeightOne/IntegralStructure.lean` | the integral-structure route (not the driver) |
| modular-curve geometry | `ModularCurve/*`, `AlgebraicCurve/*` | the shared geometry cone |

| landed (E-S-specific) | file | relevance |
|---|---|---|
| the five external facts | `Algebra/MvPolynomialHomogeneous.lean`, `ModularForms/Analytic/{StarConvexPrimitive,CuspBoundedness}.lean`, `ModularForms/ModularGroup.lean` | the whole mathlib gap of §3.3 |
| the definitions | `EichlerShimura/{BinaryForm,CoeffCohomology,EichlerIntegral}.lean` | `BinaryForm`/`binaryFormRepSL`/`binaryFormAlphaAdj`; `coeffCocycles`/`coeffCoboundaries`/`coeffParabolicCocycles`/`coeffH1par`; `IsEquivariantPrimitiveWith`/`IsEichlerIntegral` |
| the map and its injectivity | `EichlerShimura/PeriodMap.lean` | the structural `periodMap`, `periodMap_eq_coeffH1parMk`, `periodMap_injective`; nine of the twelve core nodes |
| wire test | `spec/EichlerShimuraConsumer.lean` | cross-module composition |

What remains of the E-S-specific gap:

* `coeffH1`/`coeffHeckeFun` and the Hecke correspondence
  (`heckeUpper`/`heckeConj`/`transferAux`/`heckeOperatorHom`) —
  `Def_Gamma0CoeffCohomologyEigen` and `Def_Gamma0HeckeOperatorHom`;
* the Hecke equivariance of `ES`, and core nodes #8, #11, #12 (Appendix C §C.3);
* the dimension theory (`finrank_coeffH1par_*`, `ModularCurve.genusFormula`,
  `nuTwo`, `nuThree`, `cuspCount`);
* the conjugate-linear involution and the complementarity proof;
* the integral basis of $`H^1_{par}`$ and the eigenclass layer.

See Appendix C §C.3 and
[../lean/logs/eichler-shimura-port.md](../lean/logs/eichler-shimura-port.md).

## 5. The effort relative to what landed

The honest split is:

* **Shared layer.** ~248k lines of the closure (modular-curve geometry,
  Riemann–Roch, $`J_0(N)`$/Tate arithmetic, cusp-form finite-dimensionality). The
  port already carries ~19k lines of it and needs the rest for the endgame
  regardless of the driver; the driver does not add to it except through the
  dimension theory's genus/cusp counts.
* **E-S-specific layer.** ~13,200 lines, of which ~2,731 have landed (the
  period-map milestone: §4, Appendix C §C.3); ~10,500 remain. This is the
  marginal cost of the driver.

So the baseline is: **write the E-S-specific layer (~13k lines) on top of the
already-landed Hecke/geometry infrastructure.** That is a self-contained,
well-understood body of classical mathematics (one-variable complex analysis,
group cohomology in degree one, and a dimension count), not new theory. The three
mathlib-absent lemmas are the only places where the port is not assembling
existing pieces.

## 6. What to port next

The order below is dependency-driven; each tier is checkable on its own.

1. **Definitions — done (map+injectivity share).** The three modules the
   map+injectivity cone needs — `Def_HeckeEis_BinaryFormRep`, 
   `Def_Gamma0CoeffCohomology` and `Def_HeckeEis_EichlerIntegral` — landed as
   `EichlerShimura/{BinaryForm,CoeffCohomology,EichlerIntegral}.lean`. The full
   driver still adds `coeffH1`/`coeffHeckeFun` and the Hecke correspondence
   `heckeUpper`/`heckeConj`/`transferAux`
   (`Def_Gamma0CoeffCohomologyEigen`, `Def_Gamma0HeckeOperatorHom`, ~420 lines),
   which the map+injectivity cone does not use.
2. **The analysis — done.** The five mathlib-absent nodes of §3.4 (landed in the
   generic homes of §4) and the analytic-core nodes — Eichler-integral existence,
   its transport and difference-by-a-constant, the ladder and boundedness lemmas,
   the parabolic-cocycle wrapping. **The general-weight map and its injectivity
   are complete**: the minimum cone of §3.4, ~3,400 lines, strictly containing
   Route B. The plan
   [../lean/topics/eichlerShimura/TOPIC-period-map-injectivity.md](../lean/topics/eichlerShimura/TOPIC-period-map-injectivity.md)
   is COMPLETE; the record is
   [../lean/logs/eichler-shimura-port.md](../lean/logs/eichler-shimura-port.md).
3. **The rest of the isomorphism.** `coeffH1`/`coeffHeckeFun` and the Hecke
   correspondence; the Hecke equivariance of `ES` (good and bad primes); the
   conjugate-linear involution; the integral basis; the dimension bound; and the
   complementarity that assembles the named driver `eichlerShimura_isomorphism`.
   Core nodes #8, #11 and #12 belong here (Appendix C §C.3).
4. **The optional mod-$`p`$ layer.** The eigenclass, the Eisenstein boundary and
   the projLine/retraction carrier maps. Port these only if interface 4 keeps the
   full-isomorphism branch; otherwise the intrinsic mod-$`p`$ core covers
   interface 4 and interface 1 is the only consumer (§2.2).

Stop condition: if tier 3's dimension bound turns out to need a large unported
slice of the `ModularCurve` genus/cusp cone, decide explicitly whether to port
that geometry now or to state the driver for a level where the bound is already
available.

## 7. Reproduction

```bash
cd tools/deps && python3 - <<'PY'
import sys; sys.path.insert(0, '.')
from fltdata import FltData
from prune import FltPayoff, build_removed, DEFAULT_ROOT, INTERFACES, ANALYTIC_12
d = FltData(); pay = FltPayoff(data=d)
port = pay.closure(pay.pid(DEFAULT_ROOT))
full = d.index['HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime']
R = set(build_removed(pay, "packaging", port)[0])
A12 = {d.index[q] for q in ANALYTIC_12}
C = pay.closure(full)
print('iso closure:', len(C), pay.total_lines(C))
print('  R:', len(C & R), pay.total_lines(C & R))
print('  core:', len(C & A12), pay.total_lines(C & A12))
print('  HeckeEis:', len([i for i in C if d.qual(i).startswith('HeckeEis.')]),
      pay.total_lines([i for i in C if d.qual(i).startswith('HeckeEis.')]))
for n, q in INTERFACES:
    print('interface', n, 'R-closure', len(pay.closure(d.index[q]) & R))
PY
```

## 8. Method — is the route you replaced still needed?

Both replacements in this note — C′ for route A, and route B plus the analytic core
for the parabolic/bundled packaging — raise the same question. **The frontier's cone
is the *pin's* cone**, so a node can sit on a target's shelf only because the pin's
proof reached it through the very route that has been replaced. A bottom-up "ready
shelf" therefore cannot witness independence by itself. Two tests on the docs-site
graph settle it, and neither re-reads Lean.

**Test 1 — root membership (does the target use the replaced route at all?).**
Closure is transitive, so `R ⊆ closure(T)` exactly when some node of `closure(T)`
cites `R`. The avoided route's *roots* are the whole question: if none of them lies
in the target's cone, nothing on the target's path cites them, directly or
indirectly, and the route's internal size is irrelevant.

**Test 2 — prune (what does the substitution actually save?).** Supply the
replacement statement and re-close: `prune.prunable` returns the nodes that become
unreachable, and `prune.frontier` the retained proofs that must be rewired. This is
the same instrument §3–§5 use for the packaging, applied to a replacement instead of
a removal.

```python
# tools/deps — no Lean is re-read; the graph is the docs-site's
from fltdata import FltData
from prune import FltPayoff, prunable
d = FltData()
pay = FltPayoff(data=d)

DS    = pay.pid('DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen')
ds    = pay.closure(DS)
route = pay.closure(pay.pid('CuspForm.hasIntegralStructure_of_two_le'))   # route A
roots = [pay.pid(q) for q in ('CuspForm.hasIntegralStructure_of_two_le',
                              'CuspForm.hasIntegralStructure_two',
                              'CuspForm.moduleFinite_heckeAlgebra')]

print('Test 1  roots in the target cone :', [r in ds for r in roots])
print('Test 2  prunable(target, roots)  :', len(prunable(pay.cites, DS, roots)))
print('Test 2  prunable(target, route)  :', len(prunable(pay.cites, DS, route)))
```

**Worked case (2026-10-09, the D-S column).** Route A is 657 nodes / 263,720 `S_`
lines and 420 of them / 207,667 lines lie in the D-S cone — and D-S still does not
depend on route A:

* none of route A's three roots is in the D-S cone, and `prunable(D-S, roots) = 0`:
  C′'s substitution removes nothing at all from D-S's demand;
* `prunable(D-S, route A) = 420` — the whole overlap is load-bearing for D-S, and it
  is shared geometry rather than integrality: `AlgebraicCurve` 154 / 67,427,
  `ModularCurve` 153 / 38,499, `WeierstrassCurve` 64 / 83,256, `PeriodPair`
  9 / 9,836. D-S reaches those nodes by its own paths, and route A reaching them too
  is a fact about route A;
* of the overlap, 340 nodes / 192,842 lines are already ported and 80 / 14,825 are
  still on D-S's own shelf — the latter needed for D-S's reasons, not route A's;
* the one C′-side statement the D-S cone *does* cite,
  `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast`, carries its own
  53-node / 33,719-line closure, cites no route-A root, is fully ported, and
  substituting it prunes 1 node / 183 lines. A replacement is safe exactly when this
  holds for each statement it supplies.

**Why the negative is sound and the positive is only an upper bound.** The docs-site
closure over-approximates: a proof file's `attribute [-simp]` scaffolding re-exports
its whole inlined prelude (register, scoping cautions). An over-approximation never
misses a real edge, so *absence* from a closure is a sound negative — "`T` does not
use `R`" — while *presence* only bounds the need from above. Take the independence
claim from Test 1 and the saving from Test 2. A node's presence on a shelf is not by
itself a reason to port it, and its membership in an avoided route's closure is not a
reason to avoid it either.

## Appendix A — the 33-node cohomological layer `R`

Line counts are the pin's `S_`-file lines; titles are the pin's generated English
titles. Statement files are `Theorems/Thm_<stem>.lean` with `<stem>` the
qualified name with dots replaced by underscores (pin `aa2d8b3`).

### 1. The period map (4 / 394)

| node (`HeckeEis.`) | lines | content |
|---|---:|---|
| `eichlerShimuraMap_eq_coeffH1parMk` | 48 | computed by any admissible Eichler integral |
| `eichlerShimuraMap_add` | 81 | additivity |
| `eichlerShimuraMap_smul` | 79 | ℂ-homogeneity |
| `eichlerShimuraMap_injective` | 186 | injectivity via the negative-weight form |

### 2. The two halves (5 / 2,000)

| node | lines | content |
|---|---:|---|
| `exists_coeffH1par_semilinearMap_starRingEnd` | 332 | conjugate-linear involution on $`H^1_{par}`$ |
| `isCompl_range_eichlerShimuraMap_range_conj` | 185 | the two images are complementary |
| `range_eichlerShimuraMap_inf_range_conj_eq_bot` | 1,325 | they meet only in 0 (the hard half) |
| `exists_eichlerShimura_coeffH1par_binaryFormRepSL` | 48 | the packaged isomorphism |
| `exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime` | 110 | the same with all Hecke operators |

### 3. Hecke equivariance (4 / 1,742)

| node | lines | content |
|---|---:|---|
| `exists_coeffH1par_linearMap_coeffHeckeFun` | 80 | the cohomological $`T_\ell`$ exists |
| `coeffH1par_map_heckeT_comm` | 113 | coefficient change commutes with $`T_\ell`$ |
| `eichlerShimuraMap_heckeTLin` | 907 | $`ES`$ intertwines $`T_\ell`$ (good $`\ell`$) |
| `eichlerShimuraMap_heckeULin` | 642 | $`ES`$ intertwines $`U_\ell`$ (bad $`\ell`$) |

### 4. Coefficient change and functoriality (3 / 1,142)

| node | lines | content |
|---|---:|---|
| `exists_coeffH1par_map_ringHom` | 258 | coefficient extension on $`H^1_{par}`$ |
| `exists_coeffH1par_map_of_equivariant_retraction` | 174 | equivariant retractions (interface 1) |
| `exists_coeffH1par_projLineRepSL_equiv_parabolicHoms` | 710 | Shapiro/projLine bridge |

### 5. Integral structure (9 / 3,521)

| node | lines | content |
|---|---:|---|
| `coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero` | 138 | torsion-freeness |
| `coeffH1par_binaryFormRepSL_eq_zero_of_odd` | 71 | odd $`n`$ vanishes |
| `coeffH1par_map_int_rat_injective` | 426 | $`\mathbb{Z}\to\mathbb{Q}`$ injective |
| `linearIndependent_coeffH1par_map_rat_complex` | 470 | independence persists over ℂ |
| `mem_span_range_coeffH1par_map_rat_complex` | 471 | rational classes span over ℂ |
| `exists_basis_coeffH1par_int_complex` | 316 | integral basis maps to a ℂ-basis |
| `span_range_coeffH1par_map_int_complex_eq_top` | 54 | integral classes span |
| `exists_ne_zero_smul_eq_coeffH1par_map_int_rat` | 789 | nonzero integral multiples |
| `exists_eq_prime_smul_of_coeffH1par_map_eq_zero` | 786 | mod-$`p`$ kernel is $`p`$-divisible |

### 6. Dimension theory (4 / 1,180)

| node | lines | content |
|---|---:|---|
| `finrank_coeffH1par_top_add_le` | 393 | Euler-characteristic bound for $`\mathrm{SL}_2(\mathbb{Z})`$ |
| `finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced` | 500 | Shapiro monotonicity |
| `finrank_coeffH1par_le_two_mul_dimFormula` | 120 | $`\dim H^1_{par} \le 2\dim S_{n+2}`$ |
| `finrank_coeffH1par_zero_le_two_mul_genusFormula` | 167 | weight-2 bound $`2g`$ |

### 7. Mod-$`p`$ eigenclass and boundary (4 / 810)

| node | lines | content |
|---|---:|---|
| `exists_coeffH1par_int_modp_eigenclass_of_eigenform` | 205 | integral eigenclass mod $`p`$ |
| `exists_coeffH1par_int_modp_eigenclass_of_ideal_heckeAlgebra` | 71 | from a maximal Hecke ideal |
| `exists_coeffH1par_binaryFormRepSL_eigenclass_of_ideal_heckeAlgebra_of_ne_two` | 61 | char-$`p`$ eigensystem (interface 1) |
| `exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1` | 473 | the Eisenstein boundary is form-theoretic |

## Appendix B — the 12-node analytic core

`S_` lines (the first ten are in the driver's closure).

| # | node (`HeckeEis.`) | `S_` lines | content |
|---|---|---:|---|
| 1 | `exists_isEichlerIntegral` | 102 | existence of the Eichler integral |
| 2 | `isEquivariantPrimitiveWith_of_isEichlerIntegral` | 46 | EI + slash-invariance $`\Rightarrow`$ primitive |
| 3 | `IsEichlerIntegral.slash` | 191 | EI transported by $`\delta`$ |
| 4 | `IsEichlerIntegral.exists_sub_eq_const` | 172 | two EI differ by a constant |
| 5 | `IsEichlerIntegral.eq_zero_of_eval_eq_const` | 92 | constant eval of an EI forces $`g = 0`$ |
| 6 | `IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv` | 305 | iterated $`\partial_1`$ identity |
| 7 | `IsEichlerIntegral.isBoundedAtImInfty_eval` | 178 | growth at the cusp |
| 8 | `IsEichlerIntegral.binarySubst_adjugate_comp_smul` | 184 | EI transported along the Hecke correspondence |
| 9 | `IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries` | 44 | primitives differing by a constant give coboundary differences |
| 10 | `jFactor_pow_mul_eval_binaryFormRepSL` | 74 | automorphy-factor identity |
| 11 | `coeffH1Mk_cocycle_heckeTLin_modularForm` | 633 | Hecke equivariance of the period class (target lemma only) |
| 12 | `modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero` | 280 | period injectivity (target lemma only) |

## Appendix C — the core's definition layer and the pin's two cohomologies

Salvaged (2026-09-28) from the retired `TOPIC-relaxed-analytic-core.md`, removed
when interface 3 stopped being the driver. Its "relaxed payout" framing is
dropped; what is kept is the part still about the driver: the definition-layer
map behind the 12-node core (Appendix B), the correspondence between the pin's
hand-rolled degree-1 cohomology and mathlib's, and the status of the core after
the period-map milestone.

### C.1 The definition-layer map of the core

The 12 core nodes resolve transitively to nine `Definitions/Def_*.lean` modules
(1,449 lines / 214 declarations). Seven are actually needed (1,174 lines); the
two projective-line modules enter only through `Def_HeckeEis_BinaryFormRep`'s
`Eval` section and are not used by the core.

| `Def_` lines | decls | module | role | status |
|---|---:|---|---|---|
| 304 | 44 | `Def_Gamma0HeckeOperatorHom` | Hecke correspondence: `alphaMat`, `heckeUpper(SL)`, `heckeConj(SL)`, `gammaZeroRed`, `transferAux`, `resHom`, `coresHom`, `pullbackHom`, `heckeOperatorHom` | needed by the full driver (not by map+injectivity) |
| 204 | 50 | `Def_ModularForm_HeckeOperator` | `heckeMatrix`, `heckeDiagMatrix`, `heckeT`/`heckeU` on functions | landed (`ModularForms/Defs/HeckeOperator.lean`) |
| 182 | 26 | `Def_ProjectiveLineMatrixAction` | projective-line matrix action, `projLineRepSL`, `projLineAlphaAdj` | **not needed** (Eval-section ballast) |
| 153 | 21 | `Def_Gamma0CoeffCohomology` | hand-rolled degree-1 cohomology, the parabolic layer, `coeffHeckeFun` | landed minus the Hecke section (`EichlerShimura/CoeffCohomology.lean`) |
| 149 | 19 | `Def_HeckeEis_EichlerIntegral` | `linePow`, `jFactor`, `IsEquivariantPrimitiveWith`, `IsEichlerIntegral`, `eichlerShimuraMap` | landed minus `eichlerShimuraMap` (`EichlerShimura/EichlerIntegral.lean`) |
| 140 | 16 | `Def_HeckeEis_BinaryFormRep` | `BinaryForm`, `binarySubst`, `binaryFormRepSL`, `binaryFormAlphaAdj`, + `Eval` | landed minus `Eval` (`EichlerShimura/BinaryForm.lean`) |
| 112 | 14 | `Def_Gamma0CoeffCohomologyEigen` | `coeffH1`, `coeffH1Mk`, `coeffH1parToH1`, `IsCoeffHeckeOnH1`, `IsEigensystemH1`, `binaryFormRep` | needed by the full driver; not yet ported |
| 112 | 12 | `Def_ModularForm_HeckeOperatorForms` | `heckeTLin`/`heckeULin` on `ModularForm`/`CuspForm` | landed (`ModularForms/HeckeOperatorForms.lean`) |
| 93 | 12 | `Def_ModularCurve_ProjectiveLine` | `IsUnimodularRow`, `UnimodularRow`, `ProjectiveLine`, `borel` | **not needed** (Eval-section ballast) |
| **1,449** | **214** | | | **7 modules / 1,174 lines actually needed** |

The 275 lines of projective-line ballast are shared with retained endgame API:
`binaryFormEval` is cited by `CuspForm.heckeLocal.*` and interface 5, so it stays
in the port — but it belongs with the projective-line evaluation, not with the
core's binary-form representation, and the port split it accordingly.

### C.2 The pin's two cohomologies

The pin carries **two unrelated cohomology developments**:

1. **The hand-rolled one on this path.** `HeckeEis.coeffCocycles` /
   `coeffCoboundaries` / `coeffH1` (and the parabolic `coeffH1par`) are built from
   `Submodule` / `LinearMap` / `Submodule.Quotient` alone: 1-cocycles
   $`z(gh) = z(g) + \rho(g) z(h)`$ as a submodule of $`G \to V`$, 1-coboundaries
   as the range of $`v \mapsto (\rho(g) v - v)_g`$, and their quotient. It uses
   mathlib's `Representation` but imports nothing from
   `Mathlib.RepresentationTheory.Homological`.
2. **Mathlib's group cohomology, used elsewhere.** The Galois/Selmer side has 49
   `Definitions/Def_GroupCohomology_*.lean` modules and 2,033 files referencing
   `groupCohomology`/`cocycles₁`/`H1π`/`H1Iso`; the endgame imports mathlib's
   `RepresentationTheory.Homological.GroupCohomology.*` regardless.

The two never meet in the pin: the core's files contain zero occurrences of
`groupCohomology`, `cocycles₁`, `coboundaries₁`, `H1π`, `Rep.of` or
`inhomogeneousCochains`. But there is an exact mathematical correspondence, with
$`A := \mathrm{Rep.of}\ \rho`$:

| pin (`HeckeEis.`) | mathlib | relationship |
|---|---|---|
| `coeffCocycles ρ` | `groupCohomology.cocycles₁ A` | same submodule of $`G \to A`$; identities differ by `add_comm` |
| `mem_coeffCocycles_iff` | `mem_cocycles₁_iff` | same statement |
| `coeffCoboundaryMap ρ` | `d₀₁ A` | same linear map |
| `coeffCoboundaries ρ` | `coboundaries₁ A` | same `LinearMap.range` |
| `coeffCoboundaries_le_coeffCocycles` | `coboundaries₁_le_cocycles₁` | same |
| `coeffH1 ρ` | `H1 A` (`H1Iso : H1 A ≅ cocycles₁ A ⧸ coboundaries₁ A`) | isomorphic, **not** defeq |
| `coeffH1Mk ρ` | `H1π A` | the quotient map |
| `coeffH1Mk_eq_zero_iff` | `H1π_eq_zero_iff` | same |
| trivial coefficients: `coeffCoboundaries 1 = ⊥`, `coeffH1 1 ≅ Additive Γ₀ →+ K` | `coboundaries₁_eq_bot_of_isTrivial`, `H1IsoOfIsTrivial` | **already in mathlib** — the carrier bridge of §1.2 |
| `IsParabolicCocycle` / `coeffParabolicCocycles` / `coeffH1par` / `coeffH1parMk` / `coeffH1parToH1` | none | pin-specific parabolic sub-quotient |
| `coeffHeckeFun` / `IsCoeffHeckeOnH1` / `heckeOperatorHom` / `transferAux` / `coresHom` / `resHom` / `pullbackHom` | none | pin-specific Hecke action |
| `IsEigensystemH1` | none | the contract |

**Port decision (recorded).** The port kept the hand-rolled definitions (the
low-risk option): `EichlerShimura/CoeffCohomology.lean` is written over
`coeffCocycles`/`coeffCoboundaries`/`coeffParabolicCocycles`/`coeffH1par`, and
`groupCohomology` appears nowhere in `FLTForHuman` or `Reserve`. The landed
`periodMap` takes values in the hand-rolled `coeffH1par`, so this is the current
interface, not a legacy one. The **middle path** remains open and is the cheap
way to keep mathlib's trivial-coefficient bridge available: a small compatibility
module proving `coeffCocycles ρ = cocycles₁ (Rep.of ρ)`,
`coeffCoboundaries ρ = coboundaries₁ (Rep.of ρ)` and
`coeffH1 ρ ≃ₗ H1 (Rep.of ρ)`. The Hecke action and the parabolic quotient are
pin-specific under either option. Recorded because a later carrier switch would
go through exactly this bridge.

### C.3 Status after the period-map milestone (2026-09-28)

Nine of the twelve core nodes are now ported (build-green, `sorry`-free,
checker-registered), in `FLTForHuman/ModularForms/EichlerShimura/` plus the
generic homes of §C.1:

* **landed: #1–#7, #9, #10** — the Eichler-integral existence, slash,
  difference-by-a-constant, the iterated $`\partial_1`$ identity, the
  ladder/boundedness lemmas, the equivariant-primitive bridge, the
  automorphy-factor identity, and the coboundary-difference bridge;
* **remaining for the full driver: #8** `IsEichlerIntegral.binarySubst_adjugate_comp_smul`
  (184, Hecke transport), **#11** `coeffH1Mk_cocycle_heckeTLin_modularForm`
  (633, Hecke equivariance of the period class) and **#12**
  `modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero` (280, the non-parabolic
  period injectivity).

Difficulty notes for the three (source-read, pre-port): #11 is the highest —
double-coset Hecke correspondence (`alphaMat`/`betaGL`/`transferAux`, Bézout and
coset transversals, slash bookkeeping, one analytic input), long but elementary,
the risk being bookkeeping volume rather than mathlib gaps; #12 is high, its
shape risk the `ModularForm` structure fields at negative weight (`perForm`,
`eq_const_of_weight_zero` / `isZero_of_neg_weight`); #8 is medium-high, adjugate
identities plus a chain rule with determinant. The period-map milestone
deliberately left #8–#12 out: the map-plus-injectivity cone does not need them.

### C.4 Stop condition (still live)

The core needs only **degree-1** group cohomology on `coeffCocycles` /
`coeffCoboundaries`. Stop and report if a candidate must build a genuine
$`H^1(\Gamma_0, \mathrm{Sym}^n)`$ (Kuga–Sato, de Rham comparison, or a
`CohCarrier.H1` identification at $`n \gt 0`$). The retired topic's
"route B must not be treated as a substitute for the 12" condition is dropped
with the relaxed framing.
