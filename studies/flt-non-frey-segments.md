# Survey: the segments of FLT that are not specialized to the Frey curve

Which parts of the FLT development are *not* about the one curve
$`y^2 + xy = x^3 + \frac{b^p-1-a^p}{4}x^2 - \frac{a^pb^p}{16}x`$, what each part
proves, and how reusable it is. Everything is read from the pinned clone
`anthropics/fermats-last-theorem@aa2d8b3`; the measurements come from the
docs-site dependency graph the repository already ships
(`html/data/{meta,edges}.js`), re-exposed by this project's `tools/deps`.

This is the **repo-wide** companion to
[flt-function-field-theory-and-mathlib.md](flt-function-field-theory-and-mathlib.md),
which surveys one segment (the function-field curve layer) in depth, and to
[flt-ffg-field-theory.md](flt-ffg-field-theory.md), which surveys one cone.
It asks the complementary question: *everything else.*

Conventions follow [../AGENTS.md](../AGENTS.md); FLT citations are public URLs at
the pinned commit `aa2d8b3`.

## 0. The question and the short answer

Question: FLT proves one theorem about one curve. How much of the development is
specialized to that curve, and what is the rest?

Answer: the Frey-specific layer is a **thin cap — 64 theorem nodes and about
12.3k lines out of 29,511 nodes and about 13.5M lines** (≈0.09% of the code).
The remaining 99.9% is general infrastructure. But "not specialized to the Frey
curve" is true in three quite different strengths, and conflating them is the
main way to misread the tree:

1. **Generic theory mathlib lacks.** Stated for arbitrary objects, reusable as
   a library in principle: the function-field curve layer (`AlgebraicCurve`),
   the division-polynomial / EDS / Vélu arithmetic of `WeierstrassCurve`, the
   formal-group and $`p`$-divisible layers, group cohomology and Hopf orders,
   the Kummer / cyclotomic PID material. This is where the port has already
   gone.
2. **General statements proved only in the shape the Frey argument needs.**
   `WeierstrassCurve.modularity_of_semistableModel` is about *any* semistable
   integral model, but with no control of the level and no statement about
   $`L`$-functions; the lifting theorems are only at $`p = 3`$ and $`p = 5`$ with
   level conditions; Langlands–Tunnell only in Tunnell's octahedral case; Ribet
   only at conductor-supported levels; Mazur only step three. Not Frey-specific
   — but not a library either. `PROOF-PATH.md`'s closing section *"Exact
   strength of the named steps"* is the authoritative list.
3. **This proof's own constructions, parked in general namespaces.**
   Čerednik–Drinfeld uniformisation, Drinfeld curves, the 3–5 switch and its
   Rubin–Silverberg family, the Hecke carriers and $`\theta`$-cycles of
   `CohCarrier`. They mention no Frey curve, but they exist only to run this
   argument.

The family sizes, with a deliberately single-assignment bucketing (several
namespaces serve two route steps, so the assignment is a judgment — see §4):

| family | nodes | proof lines | share | principal namespaces |
|---|---:|---:|---:|---|
| Frey cap | 64 | 11,300 | 0.1% | `FreyPackage`, `FreyCurve` |
| Function-field curve layer | 2,351 | 806,509 | 6.8% | `AlgebraicCurve`, `ValuationSubring`, `IsLocalRing` |
| Elliptic arithmetic / EDS / Vélu | 1,003 | 372,091 | 3.1% | `WeierstrassCurve` |
| Mazur / modular curves | 12,604 | 4,509,574 | 37.8% | `ModularCurve`, `AlgebraicGeometry`, `GoodReductionJacobian`, `MvFormalGroup`, `PDivisibleGroup`, `FormalGroup` |
| Modularity / automorphic input | 6,256 | 3,996,227 | 33.5% | `AutomorphicForm`, `LanglandsTunnell`, `CuspForm`, `ModularForm`, `NumberField`, `M4aHerbrand`, `ArtinL`, `Rep` |
| Galois deformations / patching | 2,234 | 617,081 | 5.2% | `GaloisRep`, `Deformation`, `ResidualGaloisRep`, `GaloisRepAdic`, `PadicAlgCl`, `groupCohomology`, `HopfAlgebra`, `Algebra` |
| Ribet / Čerednik–Drinfeld | 2,907 | 1,056,484 | 8.8% | `CerednikDrinfeld`, `QuaternionAlgebra`, `DrinfeldCurve`, `NeronModelInfra`, `TateCurve` |
| everything else | 2,092 | 574,123 | 4.8% | mathlib-shadowing namespaces (`Polynomial`, `Module`, `Ideal`, …) |
| **total** | **29,511** | **11,943,389** | | |

One segment is **invisible to namespace bucketing** and hides inside "everything
else": the Kummer / small-exponent block is 8 files and **7,272 proof lines**
(`S_flt_regular.lean` 4,242, `S_fermatLastTheoremFive.lean` 1,989, the three
$`\mathrm{PID}`$ files 996, three wrappers 45) but only about eight nodes, all
top-level or `IsCyclotomicExtension`. §3.7 measures it by file.

Proof lines are the sum of the `P2M/Sol/S_*.lean` files of the namespace's
theorem nodes; they include the generated `attribute [-instance]` preamble, so
they are a consistent *proxy* for content, not a measure of mathematical work.

## 1. Method, and how to reproduce

The graph is the one the docs site builds:

* a **node** is a theorem module, named by its qualified theorem
  (`FreyPackage.level_lowering_to_two`);
* `cites(A, B)` means `P2M/Sol/S_A.lean` contains `import Theorems.Thm_B`; this
  is the import edge, which over-approximates logical dependence;
* the **namespace** is the first dot-component of the name — the nearest thing
  the tree has to a table of contents, and the unit the docs site's Areas page
  (`html/areas/index.html`) groups by.

Measurements used below, all reproducible from the public repo:

```bash
# line counts
wc -l --files0-from=<(find P2M/Sol        -name '*.lean' -print0) | tail -1   # 11,943,389
wc -l --files0-from=<(find Theorems       -name '*.lean' -print0) | tail -1   #  1,276,305
wc -l --files0-from=<(find Definitions    -name '*.lean' -print0) | tail -1   #    279,497

# namespace sizes (nodes)
#   parse html/data/meta.js -> window.FLT_META.names, bucket by first component

# upward closure of the Frey nodes: which theorems transitively import a Frey node
#   BFS on reverse edges from {names starting FreyPackage./FreyCurve.}
```

`tools/deps/explore.py <name>` prints the auto-generated English statement, the
Lean statement, direct premises, deeper premises and the path to
`fermat_last_theorem`; `tools/deps/next.py <note>` walks the other way. The
repo-wide survey of §3.1 was produced the same way.

## 2. The Frey cap: where the specialization actually is

The Frey-specific *definitions* are small and easy to enumerate:

* `Definitions/Def_FLTPrelim_FreyPackage.lean` (97 lines) — the `FreyPackage`
  structure and the curve $`E_P`$;
* `Definitions/Def_FreyCurve_Basic.lean` plus the 17
  `Definitions/Def_FreyPackage_*.lean` files (`IsConductorLevel`,
  `LoweringAt`, `ModMCarrier_*`, `MazurEichlerShimuraFamily`, …) — together
  1,016 lines;
* about 117 further Frey-specific lines inside the six `Def_FLTPrelim_*`
  files (the other four — `GaloisRep`, `ModularRep`, `Modularity`,
  `Ramification` — are general).

The Frey-specific *theorems* are 64 nodes: 59 in namespace `FreyPackage` and 5
in `FreyCurve`, totalling 11,300 proof lines. The landmarks are
`FreyPackage.of_counterexample`, `FreyPackage.no_frey_package`,
`FreyPackage.Mazur_Frey`, `FreyPackage.frey_isModular`,
`FreyPackage.level_lowering_to_two` and the exponent bookkeeping
`FreyPackage.fermatLastTheoremFor_of_five_le`.

Two refinements matter:

* **The upward closure is 131 nodes** — i.e. only 131 of 29,511 theorem nodes
  (0.44%) transitively cite a Frey node. Of those, 67 live in general
  namespaces: the Frey-glue lemmas written for the modularity lifting
  (`WeierstrassCurve.isResiduallyModularOfLevel_*`), level raising
  (`LevelRaising.qNewSupport_*`), Hecke carriers (`CohCarrier.*`), residual
  representations (`ResidualGaloisRep.exists_taylorWilesPrimes_*`) and
  quaternionic/ordinary conditions. These are the real "Frey-specific but not
  in the Frey namespace" content, and they are a large part of why the
  modularity segment is shaped the way it is.
* **Even the namespace heuristic over-counts.** For example
  `FreyPackage.exists_inertia_cycloPinned_ne_one_v2` is a general lemma about
  inertia acting on a cyclotomic twist, parked in `FreyPackage` because that is
  where it was first needed; its only direct consumer is
  `GaloisRepAdic.exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt`,
  from which `WeierstrassCurve.modularity_of_semistableModel` descends. So 64 is
  an upper bound on the Frey-specific theorem count.

`PROOF-PATH.md` §2 describes the cap's role: `no_frey_package` is assembled
from exactly four theorems — irreducibility, modularity, level lowering, and
$`S_2(\Gamma_0(2)) = 0`$.

## 3. The non-Frey segments, family by family

The order below follows the route: Mazur's irreducibility argument, then
modularity, then level lowering; the generic layers come first because they
underlie all of them. Node and proof-line counts are namespace sums from §1.

### 3.1 Function-field curve layer — 2,351 nodes / 806,509 lines

Principal namespaces `AlgebraicCurve` (1,577 nodes, 618,916 proof lines,
72 definition modules / 21,105 lines), `ValuationSubring` (337), `IsLocalRing`
(181), `IsDiscreteValuationRing` (78), `IsDedekindDomain` (57),
`TwoChartCech` (37), `RegularSingular` (13).

This is a scheme-free, function-field-first development of the theory of
curves: places and valuations, the local ring and its completion, divisors and
$`\mathrm{Pic}^0`$, correspondences and push–pull, differentials, residues,
Riemann–Roch, repartitions/adeles, the Jacobian and the Weil pairing,
semistable models and Deligne–Rapoport annuli. It is built because mathlib has
essentially none of it (`Place`, `Divisor`, `genus`, Riemann–Roch, Weil
pairing are all absent; the survey
[flt-function-field-theory-and-mathlib.md](flt-function-field-theory-and-mathlib.md)
§4 measures this ingredient by ingredient).

Genericity: **highest in the repo.** Stated over an arbitrary curve over an
arbitrary field, with no scheme language and no modular curve in sight. This is
the segment this project has already ported end to end
(`FLTForHuman/AlgebraicCurve/`, SET 1 + SET 2 + the divisor-exchange capstone;
the statement checker reports 618 identical declarations).

### 3.2 Elliptic arithmetic, EDS and Vélu — 1,003 nodes / 372,091 lines

Principal namespace `WeierstrassCurve` (61 definition modules / 17,899 lines).
But note at once: **`WeierstrassCurve` is not one segment.** Its files span at
least four subjects —

* division polynomials, elliptic nets, `IsEllipticSequence`, the
  multiplication formula, $`n`$-torsion cardinality (`EDSEngine`,
  `DivPolyMulFormula*`, `KernelIdeal`, `KernelPolynomial`, `TorsionIntegral`);
* Vélu's formulas and cyclic quotients (`Velu*`, `CyclicQuotientJ`,
  `KohelQuotient`, `LegendreModulus`, `LevelThreeModulus`);
* Drinfeld level structures and Frobenius/Hasse invariants
  (`DrinfeldBasis*`, `DrinfeldLevelFunctor*`, `HasseInvariant`,
  `FrobeniusCardHom`);
* the modularity-lifting and 3–5-switch interface (`ModularityLifting*`,
  `ThreeFiveSwitchConditioned`, `Semistability`, `ConductorLevel`).

The first is fully generic and is the subject of this project's `Elliptic/`
port (the $`\#E[n] = n^2`$ development and its EDS engine); the second is
generic isogeny arithmetic; the third and fourth are proof-shaped.

Mathlib supplies the Weierstrass curve object and its affine point group, the
division polynomials $`\psi`$, $`\varphi`$, $`\Psi\mathrm{Sq}`$, $`\mathrm{pre}\Psi_4`$
and `normEDS`, and (in v4.33) the predicates `IsEllipticNet`/`IsEllipticSequence`
— but it does **not** prove `normEDS` is an elliptic sequence. That gap is
exactly what the repo fills (`IsEllSequence'.normEDS` and the divisibility /
`redInvar` refinements, over a vendored v4.30 compatibility layer), and it is
the most obviously mathlib-upstreamable part of the whole development.

### 3.3 Mazur / modular curves — 12,604 nodes / 4,509,574 lines

The largest family by a wide margin. Principal namespaces:

| namespace | nodes | proof lines | what it is |
|---|---:|---:|---|
| `ModularCurve` | 7,711 | 3,369,150 | $`X_0(N)`$: models, q-expansions, Hecke operators, Jacobian, Eisenstein quotient |
| `AlgebraicGeometry` | 3,322 | 679,274 | the scheme/cohomology substrate Mazur's argument is stated in |
| `GoodReductionJacobian` | 674 | 168,067 | abelian schemes, good reduction, Néron models |
| `MvFormalGroup` | 166 | 73,706 | Artin–Hasse, Witt vectors, formal group laws |
| `WeierstrassProjModel` | 173 | 51,868 | projective models and their group law |
| `PDivisibleGroup` | 138 | 44,985 | $`p`$-divisible groups, Tate modules, Cartier pairing |
| `HeckeEis` | 130 | 44,516 | Eichler integrals, periods, Eisenstein series |
| `MvPowerSeries` | 81 | 33,568 | multivariate power series |
| `MvPolynomial` | 99 | 24,618 | multivariate polynomials |
| `FormalGroup` | 78 | 14,234 | formal group laws |
| `WittVector` | 32 | 5,588 | Witt vectors |

The mathematical arc is: build $`X_0(N)`$ as a curve with a model and a
$`q`$-expansion field, build its "Jacobian" — which in this development is
`JZero N := Pic⁰` of the modular function field, a degree-zero divisor class
group, not a Jacobian-variety scheme; a two-chart integral scheme model of the
curve exists separately behind an abstract `CurveModel` interface — define the
Hecke operators along correspondences and prove they commute
(`ModularCurve.heckeOperatorsCommuteBar`, proved for every $`N`$), form the
Eisenstein ideal and quotient, and run Mazur's step-three argument. That last is
stated for an **arbitrary** integral Weierstrass curve
(`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt`): a rational
$`p`$-torsion point off the identity component at 2 and 3 is off it at every
multiplicative $`\ell \ne p`$. The Frey-specific content is only the
instantiation (`FreyPackage.Mazur_Frey`, and `FreyPackage.frey_no_cofixed_large`,
1,260 proof lines). Around it sit the formal-group, $`p`$-divisible,
Dieudonné and good-reduction layers needed for the $`p`$-adic arguments.

Genericity: `ModularCurve` and the abelian-scheme/formal-group layers are
generic theory in the sense of (1) — but stated for $`X_0(N)`$ and abelian
varieties, i.e. at the level of generality the proof needs, not as a reusable
modular-curves library. The namespace is also heavily shared: the docs site
assigns 3,995 of its 7,711 theorems to the modularity step and 1,975 to level
lowering, against only 432 to irreducibility. The Eisenstein-ideal endgame
(`FreyPackage.frey_no_cofixed_large` and the `mazurStepThree` chain) is (2):
general in object, proof-shaped in strength (only step three; general Mazur
theorems on rational isogenies and torsion are not proved).

Mathlib has schemes, elliptic curves, and some abelian-variety language; it has
no Jacobian variety or Picard scheme (its `Jacobian` module is Jacobian
coordinates; its `PicardGroup` is ideal classes), no modular curve $`X_0(N)`$,
no Hecke action, no formal groups.

### 3.4 Modularity and the automorphic input — 6,256 nodes / 3,996,227 lines

Principal namespaces: `AutomorphicForm` (2,336 nodes, 1,477,733 lines,
106 definition modules / 17,610 lines), `LanglandsTunnell` (1,543 / 1,476,628,
84 / 13,463), `NumberField` (766 / 354,474 — the number-field and adelic
machinery, *not* the Kummer segment of §3.7), `CuspForm` (692 / 296,147),
`M4aHerbrand` (148 / 91,755), `ModularForm` (156 / 58,619), `Rep` (188 /
24,115), `MeasureTheory` (132), `LT` (50), `LocalNewvector` (22),
`CuspidalType` (45), `ModPForms` (65), `ArtinL` (36), `Ihara` (36),
`RubinSilverberg` (41).

This is the analytic/automorphic engine of Wiles's argument: adelic automorphic
representations and their L-functions, the adelic topology and idèle-class
machinery shared with the Kummer argument (`M4aHerbrand`, `ArtinL`), local
newvectors and cuspidal types, mod-$`p`$ cusp forms, and then Langlands–Tunnell in the
weight-one octahedral case used by Wiles
(`LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift`),
followed by multiplication by an Eisenstein series and Deligne–Serre lifting to
weight two. The apex is `WeierstrassCurve.modularity_of_semistableModel`,
stated for an **arbitrary** `W : WeierstrassCurve ℤ` with $`\Delta \ne 0`$ and
`W.IsSemistableModel` — no `freyCurve` occurs anywhere in it, and the Frey
content is only the one-file reduction `FreyPackage.frey_isModular`. It is also
the tree's centre of mass: **27,796 of the 29,511 theorem nodes lie below it**
(94%). The predicates it uses (`IsModular`, `IsResiduallyModular`,
`ModRepIsIrreducible`, `ThreeFiveSwitchCurve`) are all curve-generic.

Genericity: mostly (1)/(2). The automorphic and local representation theory is
general but developed in the specific form the proof consumes; the
Langlands–Tunnell theorem is proved only for surjective odd octahedral
$`\bar\rho_3`$ with cyclotomic determinant (see `PROOF-PATH.md`).

Mathlib has cusp forms, $`\Gamma_0(N)`$, $`q`$-expansions and modular forms;
it has no automorphic representations, no Artin L-functions, no Langlands–
Tunnell.

### 3.5 Galois deformations and Taylor–Wiles patching — 2,234 nodes / 617,081 lines

Principal namespaces: `groupCohomology` (361 / 85,776),
`HopfAlgebra` (333 / 111,714), `Algebra` (302 / 51,836), `GaloisRepAdic`
(135 / 31,061), `GaloisRep` (127 / 48,680), `Deformation` (120 / 41,094),
`ResidualGaloisRep` (92 / 21,295), `PadicAlgCl` (39 / 9,543), `AdicCompletion`
(37 / 6,753), plus `Module`, `Matrix`, `Ideal`, `ExtCitation`.

The content is the $`R = T`$ machinery: residual Galois representations and
their absolute irreducibility, deformation rings and their representing
functors, Hopf orders and Dieudonné data, $`p`$-adic Galois representations
with ordinary conditions, group cohomology and the Hecke carriers, and
Taylor–Wiles patching in Diamond's formulation
(`GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum`,
`Algebra.PatchingDatum.nonempty_patchingLevel_bot`). On top sit the two
level-conditioned modularity-lifting theorems at $`p = 3`$ and $`p \in \{3,5\}`$
and the 3–5 switch.

Genericity: (1) for the cohomological and Hopf/Dieudonné layers, (2) for the
lifting theorems. Mathlib has group cohomology (its own namespace, which FLT's
`groupCohomology` extends) and Hopf algebras; it has no Galois deformation
theory and no patching.

### 3.6 Ribet and Čerednik–Drinfeld — 2,907 nodes / 1,056,484 lines

Principal namespaces: `CerednikDrinfeld` (2,376 / 840,428, 83 definition
modules / 13,966 lines), `QuaternionAlgebra` (302 / 104,405),
`NeronModelInfra` (96 / 34,982), `DrinfeldCurve` (71 / 27,565), `TateCurve`
(57 / 29,404), `QuadraticForm` (5 / 19,700 — the local–global principle for
$`-ax^2-by^2+abz^2`$ used by the quaternion-algebra norm computations).

This is level lowering in the form the proof needs. The general statement is
`WeierstrassCurve.IsResiduallyModularOfLevel` (`Def_FLTPrelim_ModularRep.lean`):
$`W`$ *arises from* a weight-2 eigenform on $`\Gamma_0(M)`$ modulo a maximal
ideal over $`p`$ — a congruence of traces, not an isomorphism of
representations. Two general prime removals sit on top:

* the **odd-prime step** — a squarefree $`q \mid M`$, $`q^2 \nmid M`$ with
  $`\bar\rho`$ unramified at $`q`$ is removed (`…_div_of_isUnramifiedAt_sqf`);
* the **$`p`$-step** (Mazur–Ribet) — for $`p \ge 5`$ with finite $`p`$-torsion at
  $`p`$ (`…_div_of_isPeuRamifieeAt_of_five_le`).

Behind them is a Mazur / toric-dichotomy engine
(`ModularCurve.mazurPrinciple_of_ne_one_of_toricDichotomy`,
`ModularCurve.exists_toricDichotomyData_jZero`), the `RibetLevelLowering.*`
character-group endgame and `RibetEndgame.ExchangeData`; Čerednik–Drinfeld
supplies the two-place $`p`$-torsion datum over class-set graphs
(`CerednikDrinfeld.TwoPlaceTorsionDatum`) that realises `HasLowerLevelTorsion`
for $`J_0(N)`$. The geometry is built from scratch: the Bruhat–Tits tree and
Mumford uniformisation, the Drinfeld upper half-plane, Cartier–Dieudonné
modules, Lubin–Tate theory, special formal $`\mathcal{O}_D`$-modules, a Shimura
curve model, quaternion and Eichler orders with class-set Hecke data, the
Drinfeld curve $`X_0 X_1^q - X_0^q X_1`$, the Tate curve and its defect, and the
Néron-model reading machinery.

Genericity: **the five geometry groups contain zero occurrences of
`FreyPackage`/`freyCurve`** — the whole Frey interface is about 700 lines in the
`Def_FreyPackage_*` / `Def_FLTPrelim_ModularRep` files plus the five landmark
wrappers. The two steps also use disjoint geometry: the Frey odd-prime step's
import closure contains all 83 `CerednikDrinfeld` files, and the $`p`$-step's
contains all 15 `TateCurve` files. The Mazur/toric-dichotomy linear algebra and
`RibetLevelLowering.*` are pure module theory and reusable as-is; the
level-lowering *statements* are (2) — only for the Frey representation at
conductor-supported squarefree levels, not Ribet's theorem for a general
modular mod-$`p`$ representation. Mathlib has quaternion algebras (partially)
and modular forms; it has no Čerednik–Drinfeld, Drinfeld curve, Tate curve or
Néron model.

### 3.7 Kummer and the small exponents — 8 nodes / 7,272 lines (measured by file)

This segment does not show up in namespace bucketing at all: it is
`S_flt_regular.lean` (4,242 lines, a port of the `flt-regular` project),
`S_fermatLastTheoremFive.lean` (1,989, the self-contained descent in
$`\mathbb{Z}[(1+\sqrt5)/2]`$), the three PID files
`S_IsCyclotomicExtension_Rat_{seven,eleven,thirteen}_pid.lean` (84 + 180 + 732),
and three 15-line wrappers. Its declarations are top-level (`flt_regular`,
`fermatLastTheoremFive`) or under `IsCyclotomicExtension`, so §0's table counts
it inside "everything else".

The content: `flt_regular` proves `FermatLastTheoremFor p` for every odd regular
prime (Kummer's theorem, cases I and II, with the $`(\zeta-1)`$-multiplicity
descent and Kummer's lemma through a Hilbert-90/94 package); the three PID files
show $`\mathcal{O}(\mathbb{Q}(\zeta_7))`$, $`\mathcal{O}(\mathbb{Q}(\zeta_{11}))`$
and $`\mathcal{O}(\mathbb{Q}(\zeta_{13}))`$ are principal (Minkowski bounds plus
explicit principal-prime certificates); and the exponent-5 file is a
self-contained descent. These settle exponents 5, 7, 11 and 13 outright, which
is why `FreyPackage.frey_no_cofixed_small` and `_eleven` are vacuous and the
Frey irreducibility argument only has to handle $`p \ge 17`$.

Genericity: **the most clearly standalone segment in the repo.** The
`flt-regular` files import Mathlib plus `P2M.Util` only — no `FreyPackage`, no
`WeierstrassCurve`, no `ModularCurve` — and the Frey link is one-directional
consumption. The three PID proofs are individually reusable, and the segment is
the natural first candidate for an independent port or study. Mathlib has
cyclotomic fields, class groups, `classNumber_eq_one_iff` and
`IsCyclotomicExtension.Rat.{three,five}_pid`, but neither the regular-prime
criterion nor the PID results (and the port's `Hilbert91` is not mathlib's
Hilbert 90 — it is flt-regular's own "fundamental system of units" statement).

Note the companion fact from §3.2: the EDS / division-polynomial segment is
likewise *not specialized* to Frey, but it is a dependency *of* the Frey and
Mazur arguments (`S_FreyPackage_frey_no_cofixed_large.lean` imports
`Thm_WeierstrassCurve_card_torsion_of_isAlgClosed`). "Not specialized" is not
the same as "unused".

### 3.8 The 3–5 switch and Rubin–Silverberg — 41 nodes / part of `WeierstrassCurve`

`RubinSilverberg` (41 nodes) is the explicit family of curves with
$`W'[5] \cong W[5]`$ from which `WeierstrassCurve.threeFiveSwitchCurve` and
`threeFiveAuxiliaryCurveExists` are built, together with
`WeierstrassCurve.fifteenIsogenyClassification` pinning $`c_4^3/\Delta`$ of a
curve with a rational 15-isogeny. This is (3): not Frey-specific, but purely
this proof's construction, and the least likely to be reused.

## 4. What "not specialized to the Frey curve" does not mean

Three cautions, each grounded in the tree:

* **A general statement is not a general-purpose theorem.** `PROOF-PATH.md`'s
  "Exact strength" section records that the development proves each classical
  input "in the strength the argument needs": semistable modularity with an
  uncontrolled level and no $`L`$-function statement; lifting only at 3 and 5;
  Langlands–Tunnell only octahedral; Ribet only conductor-supported; Mazur only
  step three. The names are classical; the statements are the proof's.
* **A namespace is not a segment.** `WeierstrassCurve` spans §3.2, §3.4 and
  §3.8; `NeronModelInfra` serves both §3.3 and §3.6; `AlgebraicGeometry` is
  used by both Mazur and Ribet. Any bucketing, including §0's table, is a
  judgment; the docs site's Areas page uses "mostly under (first landmark
  above)" for the same reason.
* **Size is not difficulty.** The 11.9M proof lines include the generated
  `attribute [-instance]` preamble in every file and a one-`S_`-file-per-theorem
  layout that the FFG survey measured as roughly 1.6× inflated. The
  insight-dense generic kernels are tiny by comparison — this project's
  `FieldTheory/CommonRoot.lean` is three lemmas, ~166 lines, and it is the
  engine of the whole function-field-generation cone.

## 5. Where the port already is, and candidate next targets

Already ported (all in the non-Frey region): `FLTForHuman/AlgebraicCurve/`
(§3.1), `FLTForHuman/FieldTheory/` (the generic common-root kernel),
`FLTForHuman/ModularCurve/` (the function-field-generation cone, inside §3.3),
`FLTForHuman/ModularForms/` (the level-one q-expansion principle / R1, inside
§3.4), and `FLTForHuman/Elliptic/` (the EDS / $`n`$-torsion part of §3.2).

Candidates, in rough order of "generic content per unit of proof":

1. **§3.7 Kummer / `flt-regular`.** The most self-contained non-Frey segment:
   a classical theorem, no modular curves, no Frey curve, and a documented
   upstream (`flt-regular`) to diff against.
2. **The generic parts of §3.3's `ModularCurve`.** The Hecke-operator
   commutativity and the Jacobian construction have a dedicated survey already
   ([hecke-commute-bar-survey.md](hecke-commute-bar-survey.md)) and are the
   natural next topic after the FFG cone.
3. **§3.2's Vélu / cyclic-isogeny arithmetic and §3.3's formal-group /
   $`p`$-divisible layers.** Generic, mathlib-absent, and small enough to port
   as APIs.
4. **§3.6's Bruhat–Tits / quaternion / Tate-curve geometry, and its
   `RibetLevelLowering.*` / `ExchangeData` module theory.** The geometry groups
   mention no Frey object at all and the level-lowering linear algebra is pure
   module theory; their only consumer, however, is level lowering.

§3.4 and §3.5 are the largest and least library-like: their statements are
proof-shaped (§4), so they are better study targets than port targets.

## 6. Limits of this survey

The import graph over-approximates logical dependence (the docs site flags
imports whose name never occurs in the proof); namespace bucketing is a
one-component heuristic; the family table in §0 assigns each namespace once,
which slightly distorts the namespaces that serve two route steps; proof-line
counts include boilerplate; and the "mostly under" step is a first-landmark
heuristic. The counts in §2 for the Frey cap are the most robust numbers here,
because that set is small enough to enumerate by hand.

## Sources

- FLT: <https://github.com/anthropics/fermats-last-theorem>, local clone pinned
  at `aa2d8b3`; the route is
  [PROOF-PATH.md](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/PROOF-PATH.md),
  and the per-namespace index is
  [html/areas/index.html](https://github.com/anthropics/fermats-last-theorem/blob/main/html/areas/index.html).
- Key files cited above:
  [`Definitions/Def_FLTPrelim_FreyPackage.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_FreyPackage.lean),
  [`Theorems/Thm_WeierstrassCurve_modularity_of_semistableModel.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_modularity_of_semistableModel.lean),
  [`Theorems/Thm_FreyPackage_no_frey_package.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_no_frey_package.lean),
  [`Definitions/Def_CerednikDrinfeld_BruhatTitsTree.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CerednikDrinfeld_BruhatTitsTree.lean).
- Sibling surveys:
  [flt-function-field-theory-and-mathlib.md](flt-function-field-theory-and-mathlib.md),
  [flt-ffg-field-theory.md](flt-ffg-field-theory.md).
