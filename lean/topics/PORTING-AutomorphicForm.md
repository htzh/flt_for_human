# The automorphic / adèlic foundation — a math-first blueprint

The Deligne–Serre column's §7 defers two automorphic gates behind a fixed interface. This
blueprint is the **definition foundation** those gates and the `AutomorphicForm` ready-shelf
rows stand on, and the theorem-layer step that consumes it. It is deliberately a foundation
effort: the layer is organized once, by mathematics, before anything imports it. Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

The first consumer is
`AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant` — the
weight-one smoothing headline, shelf row 3 at 508 silo lines. `frontier.py --ready` prices it
`needed 1 / 508`, but that is the `S_` file only: `--ready` is a citation-name test and cannot
see `Definitions/`. The hand-walk of §1 shows the real def closure is **14 modules / 2,544 pin
lines**, of which one was ported whole. Nothing can be *stated* before that lands, so it is the
first thing the column builds; the promotion audit of §3 then adds the piece that is cheapest
early and expensive later — a public home for the prelude the pin copies into every file of the
`isFactorizableTestFn` family.

Companions: [PORTING-DeligneSerre.md](PORTING-DeligneSerre.md) §7 (why the gates wait),
[porting-playbook.md](../porting-playbook.md) §2.1/§2.3/§2.4/§3.1/§3.2/§3.7, and the organization
precedent [deligneSerre/TOPIC-definitions-and-homes.md](deligneSerre/TOPIC-definitions-and-homes.md).

## 1. The definition closure — the measured starting point

The target's `S_` file imports four pin `Def_*` modules; walking their `Definitions/` import DAG
closes over 14 modules.

| pin module | decls | lines | port home |
|---|---:|---:|---|
| `Def_NumberField_AdelicHaar` | 25 | 205 | `NumberTheory/AdelicHaar/{Local,Adele,GeneralLinear}` |
| `Def_NumberField_AdelicLevel` | 119 | 813 | `NumberTheory/AdelicLevel/{IdealBall,Projections,Level,HeckeGen}` |
| `Def_AutomorphicForm_FactorizableTestFn` | 10 | 66 | `AutomorphicForm/Adelic/FactorizableTestFn` |
| `Def_AutomorphicForm_RightConvolution` | 5 | 37 | `AutomorphicForm/Adelic/RightConvolution` |
| `Def_AutomorphicForm_SmoothAutomorphicFnAt` | 16 | 90 | `AutomorphicForm/Adelic/SmoothAutomorphicFn` |
| `Def_AutomorphicForm_ArchType` | 24 | 189 | `AutomorphicForm/Adelic/ArchType` |
| `Def_AutomorphicForm_RowIsometryInvariance` | 12 | 210 | `AutomorphicForm/Adelic/WindowedSiegel/RowIsometry` |
| `Def_AutomorphicForm_WindowedSiegelSet` | 29 | 307 | `AutomorphicForm/Adelic/WindowedSiegel/Set` |
| `Def_AutomorphicForm_CarrierPins` | 12 | 76 | `AutomorphicForm/Adelic/CarrierPins` |
| `Def_AutomorphicForm_AdelicLsXi` | 11 | 55 | `AutomorphicForm/Adelic/{Basic,LsXi}` |
| `Def_AutomorphicForm_ConstantTerm` | 11 | 63 | `AutomorphicForm/Adelic/ConstantTerm` |
| `Def_AutomorphicForm_AutomorphicFnAt` | 8 | 71 | `AutomorphicForm/Adelic/AutomorphicFn` |
| `Def_RepTheory_SmoothVectors` | 27 | 321 | `RepTheory/SmoothVectors` |
| `Def_Deformations_ContinuousSMulDiscrete` | 5 | 41 | `RepTheory/ContinuousSMulDiscrete` |
| **total** | **314** | **2,544** | |

The statement alone names `AdelicGL2` (`AdelicLsXi:12`), `levelOne` (`AdelicLevel:589`, and its
`IsLevelOneMatrix`/`finiteLevelOne`/`idealBall`/`idealBound` chain), `finiteAdelicGL2Subgroup`
(`SmoothAutomorphicFnAt:15`) and `rightConv` (`RightConvolution:9`), whose body needs
`AdelicHaar.glBorel`/`adelicGLHaar`. The proof adds `adelicArchGLIncl` (`ArchType:122`) and the
whole `WindowedSiegel` norm/isometry chain.

**The mathematics, layer by layer** — this is the reading order and the set order of §4:

1. **Adèlic measure theory.** The completions `K_v` and their integral subrings
   (proper/compact), then `𝔸_K` (Hausdorff, Borel, additive Haar), then `GL₂(𝔸_K)` (Borel
   structure, Haar). This makes `rightConv` and every integral in the target meaningful.
2. **Adèlic level.** The level function `idealBound`, the integral finite adèles and the
   level-`N` ball, the archimedean/finite projections, the level matrices and subgroups
   `finiteLevelZero/One`, `levelZero/One`, the principal-level Weyl twist, and the Hecke
   generators (`localUnit`, `heckeGenAt`, `heckeGen`). This is the vocabulary of "level-`N`
   invariance" and of the finite subgroup `levelOne ⊓ finiteAdelicGL2Subgroup`.
3. **Representation theory.** Smooth vectors for a topological group action and the
   discrete-`SMul` class they rest on. Generic, mathlib-first, and the first real reuse in the
   layer.
4. **Automorphic vocabulary.** `AdelicGL2` and its points/central scalars; the idèle-class and
   unitary characters and the `LsXi` L²-space; the carrier-pins hypothesis bundle; unipotents,
   constant term and cuspidality; the automorphic and cusp automorphic predicates; then
   `Kf`-smoothness and the smooth automorphic predicates.
5. **Smoothing.** Right convolution, factorizable test functions, the
   `continuous_and_hasCompactSupport` premise, and the archimedean/windowed-Siegel norm and
   row-isometry estimates the non-vanishing proof consumes.

The layer is small but central: `explore.py` records these definition modules in the
*statements* of 480 (`SmoothAutomorphicFnAt`), 435 (`FactorizableTestFn`) and 356
(`RightConvolution`) theorems. It is the doorway to a **143-module / 25,727-line**
`Def_(AutomorphicForm|RepTheory|AdelicDock|Deformations)` layer, which is why the directory cut
of §2 had to be right before the other 129 modules arrive.

**Do not over-scope.** The sibling ready row
`AutomorphicForm.cosetSum_rightConv_of_isLevelSphericalOfType` imports a *different* def
closure (`CuspidalConstituent`, `ArchSpherical`, `AdelicDock_LocalEmbedding`), and the two gates
import `ProductionPinsGeneral`. This blueprint carries only the 14-module closure above; the
rest is a counted optional tail, and each future consumer gets the same hand-walk before its
order is cut.

## 2. The file plan (math clarity)

Two organizing rules drive the tree: **one directory per theory** (playbook §3.2) and **one
module per mathematical role, not one per pin file** (playbook §3.1). The pin's two mega-`Def_`
files and its mixed `AdelicLsXi` are split; the landed `AdelicHaar/Topology` stub was absorbed
rather than grown.

```
FLTForHuman/
  NumberTheory/
    AdelicHaar/
      Local.lean           -- K_v: integral subring, residue field, proper/compact
      Adele.lean           -- 𝔸_K: Hausdorff topology, Borel structure, additive Haar
      GeneralLinear.lean   -- GL₂(𝔸_K): Borel structure, Haar
      MulRightInvariant.lean -- the Haar measure on GL₂(𝔸_F) is right-invariant
    AdelicLevel/
      IdealBall.lean       -- idealBound, integral finite adèles, the level-N ball
      Projections.lean     -- 𝔸_K → K_∞ / 𝔸_K^fin, GL₂ components
      Level.lean           -- IsLevelZero/OneMatrix, finiteLevelZero/One, levelZero/One
      PrincipalLevel.lean  -- weyl, principalLevel (the Atkin–Lehner twist)
      HeckeGen.lean        -- diagOne, finIncl, localUnit, uniformizer, heckeGenAt, heckeGen
  RepTheory/
    ContinuousSMulDiscrete.lean
    SmoothVectors.lean
  AutomorphicForm/
    Adelic/
      Basic.lean               -- AdelicGL2, globalPoints, centralScalar, chiDet
      LsXi.lean                -- idèle-class/unitary chars, IsLsXiFunction/LsXiMember
      ConstantTerm.lean        -- unipotentGL2, constantTerm, IsCuspidalFn
      CarrierPins.lean         -- the hypothesis bundle
      AutomorphicFn.lean       -- LsXiMemberAt, IsAutomorphicFnAt/IsCuspAutomorphicFnAt
      SmoothAutomorphicFn.lean -- finiteAdelicGL2Subgroup, IsKfSmooth, smooth predicates
      RightConvolution.lean
      FactorizableTestFn.lean
      TestFnTop.lean           -- the continuous/compact-support premise
      TestFnNearIdentity.lean  -- the public shared family prelude (§3)
      RightConvRegularity.lean -- rightConv's continuity and C^∞ along unipotents (SET-AF5, W1)
      RightConvNeZero.lean     -- the levelOne headline                (T1)
      RightConvNeZeroPrincipal.lean -- the principalLevel headline     (T1)
      RightConvNeZeroArch.lean -- the arch-character headline          (T1)
      ArchType.lean            -- archimedean inclusion and archimedean types
      ArchWeightChar.lean      -- ArchWeightChar: determinant-one subgroup, weight chars
      ArchWeightCharTransport.lean -- transport of the weight-character data
      WindowedSiegel/
        Set.lean               -- norms, heights, the windowed Siegel set
        RowIsometry.lean       -- row isometries and their invariance lemmas
    UpperHalfPlane/            -- the landed ℍ quartet
      HyperbolicMeasure.lean
      FundamentalDomainVolume.lean
      SiegelSetCover.lean
      Gamma0FundamentalSet.lean
```

| pin module | home(s) | why split |
|---|---|---|
| `Def_NumberField_AdelicHaar` | `AdelicHaar/{Local,Adele,GeneralLinear}` | three subjects: local fields, the adele ring, the linear group |
| `Def_NumberField_AdelicLevel` | `AdelicLevel/{IdealBall,Projections,Level,HeckeGen}` | four subjects: level ball, projections, level subgroups, Hecke generators |
| `Def_AutomorphicForm_AdelicLsXi` | `Adelic/{Basic,LsXi}` | the base type `AdelicGL2` is used by everything; keeps the hub stable |
| `Def_AutomorphicForm_ConstantTerm` | `Adelic/ConstantTerm` | one subject; promote to `AutomorphicForm/Defs/` only if the ℍ branch consumes it |
| the other nine | one file each under `Adelic/` | already single-subject |

**Namespace policy.** The pin namespaces (`NumberField.AdelicHaar`, `NumberField.AdelicLevel`,
`AutomorphicForm`, `FLT.SmoothVectors`) are kept; directories carry the organization, namespaces
carry the pin fidelity the checker relies on. The one top-level pin class,
`ContinuousSMulDiscrete`, stays top-level (no namespace in the pin). The two theorem-layer homes
that are the port's own — `AutomorphicForm.TestFnNearIdentity` and
`AutomorphicForm.TestFnPrincipalLevel` — are namespaced so their generic helper names (`E`, `R`,
`J`, `fa`, `ff`) never reach the top level.

**Hubs.** `Adelic/Basic` (`AdelicGL2`), `AdelicHaar/GeneralLinear` (`glBorel`/`adelicGLHaar`),
`AdelicLevel/Projections` (`glArch`/`glFin`), `AdelicLevel/Level` (`levelOne`),
`RepTheory/SmoothVectors` and `Adelic/ConstantTerm` (`IsCuspidalFn`) are the modules everything
later imports. They are written whole, once, with the public surface the pin fixes, and later
orders treat them as frozen.

## 3. The private layer and the shared prelude home

Two questions with different answers: which pin-`private` declarations carry mathematics another
theory will state, and which repeated preludes must have one home. Both are cheap early and
re-elaborate a cone later.

### 3.1 Promotions in the definition layer

| declaration | pin home | decision |
|---|---|---|
| `continuous_glMap` | `AdelicLevel:210` (private) | **promoted.** The pin has a public twin at `Def_AutomorphicForm_BaseChangePlaces:317`, and this generic continuity of the induced `GL` map is used by every projection and embedding in the 143-module layer. It is public in `AdelicLevel/Projections` at the pin's name; `SOURCES` is ordered so the public copy wins when `BaseChangePlaces` lands. |
| `unipotent_mul_unipotent` | `ConstantTerm:11` | **stays private** — a matrix computation whose public face is `unipotentGL2_add`. |

The ℍ quartet's `box`/`cbox`/`fdoWitness`/`one_le_quadratic_form` are transcription-local measure
scaffolding whose public headlines (`volume_univ_eq_top`, `volume_band_le`, …) already carry the
mathematics, so they stay private.

### 3.2 The shared prelude home

`port_advise.py` over the `S_AutomorphicForm_exists_isFactorizableTestFn_*` family reports the
same near-identity factorisable-test-function prelude copied into every file — the strongest
unit is levelOne ↔ principalLevel at 385 lines / 41 proofs.

`AutomorphicForm/Adelic/TestFnNearIdentity.lean` is that prelude's public home: 58 declarations,
transcribed from the `TestFnNearIdentity` block of the levelOne `S_` file at
`AutomorphicForm.TestFnNearIdentity`. `SOURCES` lists the pin copies with the public
`hasArchCharacterAt` `Scaffold` block first and the private siblings after it.

The home's surface is the construction the `rightConv_ne_zero_of_*` family otherwise copies: the
archimedean homeomorphism `mixedHomeo` (and `matHomeo`/`pairHomeo`), the closed embedding `J` of
`GL₂(K_∞)` into `E F`, the determinant-adjugate `Ψ` with compact radius `R`, the bump functions
`bumpAt`/`bump₂`, the archimedean factor `fa` (`isArchTestFactor_fa`, `fa_eq`), the finite level
set `Kf` and indicator `ff` (`isFinTestFactor_ff`, `ff_mul_of_mem`), the assembled
`testFn`/`testFnR` (`isFactorizableTestFn_testFn`, `testFn_mul_of_mem`, `testFn_decomp`,
`testFn_support`, `testFn_eq_ofReal`, `testFnR_nonneg`, `testFnR_one`, `of_testFnR_ne_zero`) and
the integral bound `rightConv_ne_zero_of_bound`.

**How far the home reaches.** The prelude is *not* one block for the whole family. Diffing the
pin's copies:

- **levelOne** is the home itself.
- **principalLevel** differs only in the level-specific `Kf`/`ff`/`testFn` layer (its
  `finitePrincipalLevel` replaces `finiteLevelOne`), and in exactly two statements —
  `ff_mul_of_mem` and `testFn_mul_of_mem`, whose invariance hypothesis names `principalLevel`.
  `AutomorphicForm.TestFnPrincipalLevel` imports the home and writes only that layer.
- **hasArchCharacterAt** generalizes the prelude: `ArchProfile` — an abstract `C^∞` bump of
  compact support — replaces the concrete `bumpAt`, so `Φ₂`/`fa`/`testFn`/`testFnR` and nine of
  their lemmas take `P : ArchProfile F ρ` instead of `(ρ) (hρ)`. Thirteen signatures differ, and
  the file carries ~57 further declarations of arch-weight-character analysis
  (`sqSize`/`q`/`core`/`bump`, rotation matrices, the `sqSize_split`/`q_split`/`q_archEntries_conj`
  chain, `hasArchCharacterAt₀_rightConv_of_conj_invariant`). The port homes that as
  `AutomorphicForm.TestFnArchProfile`: the `ArchProfile` structure with its generalized family,
  the arch-character extras, and the headline; it imports the home for everything the
  generalization does not touch, plus `Adelic/ArchWeightChar{,Transport}` for the weight
  characters and `AdelicHaar/MulRightInvariant` for the right-invariance the character transfer
  uses.

`TestFnTop` keeps its own `private` `continuous_ringEquiv_mixedSpace`: importing the home there
would invert the import graph, so the copy stays (playbook §5).

## 4. The porting order, and what has landed

The def-import DAG fixes the order; each level is one work order.

| set | modules (home) | pin lines | depends on | state |
|---|---|---:|---|---|
| **D0** | `RepTheory/ContinuousSMulDiscrete`, `Adelic/{Basic,LsXi,ConstantTerm}` | 230 | mathlib only | landed |
| **D1** | `AdelicHaar/{Local,Adele,GeneralLinear}` (absorbs `Topology`) | 205 | mathlib only | landed |
| **D2** | `RepTheory/SmoothVectors` | 321 | D0 | landed |
| **D3** | `AdelicLevel/{IdealBall,Projections,Level,HeckeGen}` (grows `Projections`; promotes `continuous_glMap`) | 813 | D1 | landed |
| **D4** | `Adelic/{CarrierPins,RightConvolution,FactorizableTestFn}` | 179 | D1, D3 | landed |
| **D5** | `Adelic/{AutomorphicFn,SmoothAutomorphicFn}` | 161 | D2, D3, D4 | landed |
| **D6** | `Adelic/WindowedSiegel/{Set,RowIsometry}` | 517 | D3, D4 | landed |
| **D7** | `Adelic/ArchType` | 189 | D6 | landed |
| **H1** | `Adelic/TestFnNearIdentity` (public shared prelude) | 58 decls | D0–D7 | landed |
| **T1** | `AdelicLevel/PrincipalLevel`, `Adelic/{RightConvNeZero,RightConvNeZeroPrincipal}` | — | H1 | landed |
| **A1** | `Adelic/{ArchWeightChar,ArchWeightCharTransport}` (arch-weight-character def layer) | 313 | D7 | landed |
| **M1** | `AdelicHaar/MulRightInvariant` (right-invariance of the GL₂ Haar measure) | 326 | D1 | landed |
| **A2** | `Adelic/RightConvNeZeroArch` (the arch-character headline) | — | H1, A1, M1 | landed |
| **A5** | the right-convolution calculus: `Adelic/ConstantTerm` + `Adelic/RightConvolution` (general engine + translation law, three duplicate copies deleted) | 49 | D0, D4 | landed |
| **A5w** | `Adelic/RightConvRegularity` (the regularity headline) | 471 | A5, H1 | landed |
| **A6m** | `Adelic/FactorizableTestFnArchSmooth{,Complex}Left` (the left half of the arch chart, promoted out of `Reserve`, public) | 1,190 | D7 | landed |
| **A6** | `Adelic/ArchDerivRightConv{,Complex}` (differentiating `rightConv` along an archimedean flow) | 2,494 | A6m, A5w | landed |
| **A7** | `Adelic/BigCellExpansion` (the cone's largest node, transcribed mechanically) | 5,407 | A5w | landed |
| **A8** | `Cusp/RightConvSubrep` (the `RepTheory` ↔ `Cusp` bridge — a **composition** set, 757 net) | 3,833 | A5w | **queued** |

Two ordering notes that stay true. `ArchType` lands last among the `Def_*` modules because the
pin defines `archRowIsometryAt` over the row-isometry subgroup of D6; the port keeps that edge
rather than re-rooting the predicate. And `HeckeGen` is the one piece of D3 that is real
manipulation rather than transcription — the `localUnit`/`uniformizer`/`heckeGenAt`
restricted-product work — so it is the natural place to scout before extending the layer.

`T1` is the H1-served pair of headlines. `Adelic/RightConvNeZero.lean` states the levelOne
headline at its `Theorems/` wrapper name and proves it from the `S_` file's `solution`;
`Adelic/RightConvNeZeroPrincipal.lean` adds the principal-level layer (`AdelicLevel/PrincipalLevel`
gives `weyl`/`principalLevel`) and its headline. The two `ff_mul_of_mem`/`testFn_mul_of_mem`
statements that share a last name with the home's are resolved by the checker's dotted/pin-private
fallback.

`A2` is the third headline. Because its prelude is `ArchProfile`-parameterized rather than a copy
of the home's, it is its own module at `AutomorphicForm.TestFnArchProfile`; the wrapper name is
`AutomorphicForm.exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt`
(its conclusion also carries `HasArchCharacterAt₀` for the right convolution, not only
non-vanishing).

## 5. What remains

**The two gates.** `DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen`
and `DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen` remain the
column's automorphic input; they import `ProductionPinsGeneral`, outside this closure, and each
gets its own hand-walk before an order is cut.

**The ready shelf beyond the pair.** With the definitions and the three headlines landed, the
remaining `AutomorphicForm` ready rows and their successors become schedulable one cluster at a
time. The first cluster is **landed** (2026-11-02): [automorphicForm/SET-AF1.md](automorphicForm/SET-AF1.md),
the **cuspidal-spectrum carrier** — `Cusp/SpectrumCarrier.lean` (41 declarations, checker 41 `ok`) with
its `Cusp/SpectrumSubrep.lean` sibling (11 `ok`), the carrier-API module (5 `ok`), the pairing/slab
module (2 `ok`, which closed the 234-line slab bound the carry-forward register had held since
2026-10-18) and `NumberTheory/NumberField/TateGlobal/NormExponent.lean` (1 `ok`) — five new modules,
1,250 lines, no migration. Measured after the landing: `needed` **917 / 374,592** and one new ready
row (`CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent`, 37). The brief's §0.2 records the
read's one correction on the way in (the general norm-exponent node read as ported because the port
held only the `ℚ` statement; `twin_scan --node` verdict `relative`, FR-0092), and §1.5/§8 the landing
and its re-read.

The second cluster is **landed** (2026-11-02): [automorphicForm/SET-AF2.md](automorphicForm/SET-AF2.md),
the **adelic maximal compact subgroup** — the 331-line `Def_AutomorphicForm_AdelicMaximalCompact`
gate (38 declarations, 37 `ok`) and seven of the eight leaves it gates, in two consumer modules
(`Adelic/MaximalCompactFactors.lean` 5 `ok`, `Adelic/InducedSectionMaximalCompact.lean` 2 `ok`); 1,562
pin lines, 1,161 written. Measured after the landing: the corrected read `needed` **910 / 373,361**
and the AF ready shelf 27 rows / 6,669 silo, three of them new. Its §8 records the shadow the landing
manufactured (FR-0095).

The third is **landed** (2026-11-02): [automorphicForm/SET-AF3.md](automorphicForm/SET-AF3.md), the
**admissibility of the archimedean cut and its reproducing kernel** — four rows (998, 459, 222, 184;
1,863 silo → 1,098 net, of which 642 lines were already in the port) above a two-declaration ground,
`Adelic/ArchComponentDictionary.lean` (2 `ok`), the dictionary both consumer modules state over; the
rows are `Adelic/ArchCutSpan.lean` (3 `ok`) and `Adelic/ArchCutReproducer.lean` (1 `ok`), and the
consumer probe `spec/AutomorphicFormSetAF3Consumer.lean` is two zones at 0 errors. No definition gate:
the set's six imported `Def_` modules are complete at the declaration level (FR-0096). Measured after
the landing: `needed` **906 / 371,498** and the AF shelf 25 / 5,487 ready, 82 / 16,598 leaves — the
brief's forecast exact, and no new ready row (the set is a premise of ten rows, two of them taken to
two remaining premises). The record is its §1.5/§8; the order is
[automorphicForm/WORKORDER-AF3-proofs.md](automorphicForm/WORKORDER-AF3-proofs.md).

The fourth is **landed** (2026-11-02), ported by the manager in one session:
[automorphicForm/SET-AF4.md](automorphicForm/SET-AF4.md), the **norm side of the adèle ring** — the
idèle norm's values on unit idèles, a uniformizer and a determinant, the height's continuity and the
finite-support norm product: five shelf rows (528 silo → 109 net, 323 lines already in the port) plus
four declarations of definition ground (`finitePartUnits`, `unitIdeles`/`mem_unitIdeles_iff`,
`uniformizerIdele`, ≈27 pin lines in three `Def_` modules). It is the first column set whose shelf rows
are outside the `AutomorphicForm` namespace, chosen by **readiness return** rather than silo. Measured
after the landing: `needed` **901 / 370,970** (the forecast exact), the AF shelf 37 / 17,312, and
thirteen rows readied / 11,888 silo — ten of them writable, three carrying a definition gate the
frontier cannot see (FR-0100). The N3 glue block was promoted out of `Siegel/SlabCovering.lean` (its
private duplicate deleted) and homed on the `AutomorphicForm` side because its hypothesis is about
`AdelicGL2`; N5 went beside its engine in `WeylIntegrable/NormProdSum.lean`; and the touched
`Siegel/SlabCovering.lean` was brought to standards in the same pass (60 `-- pin:` markers → six
`spec-pin:` wires, two pre-existing dead private lemmas deleted). Its §0.4 records the one
gate the tools miss (FR-0099).

The fifth is **landed** (2026-11-02):
[automorphicForm/SET-AF5.md](automorphicForm/SET-AF5.md), the **right-convolution operator's
calculus** — `rightConv` is continuous and `C^∞` along the unipotent direction for a factorizable test
function (471 silo / 450 net, `Adelic/RightConvRegularity.lean`, landed in one worker order), on top of two rows
the manager took: the **general** `continuous_unipotentGL2` (28 silo) and the translation law
`rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` (21 silo). Three rows / 520 silo / 481 net, and
the readiness return is five rows / 7,007 silo — the two archimedean-derivative headlines
(`archDerivAt{,Complex}_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn`, 1,246 + 1,248) become
ready, so the chain SET-AF4 deferred is now the column's next set. **The set has no definition gate**
(all three rows are gate-free at the declaration level, FR-0100/FR-0099), which makes its manager's
layer pure refactor: the pin states `continuous_unipotentGL2` at a general ring, and the port held
**three** specialised copies of it in three modules — `continuous_unipotentGL2_adele` (15 lines),
`continuous_unipotentGL2'` (14) and a `private continuous_unipotentGL2` (13) — so the general statement
was written once in `Adelic/ConstantTerm.lean` (the module that defines `unipotentGL2`) and all three
were deleted, 36 lines of specialised proof. That also **closes the FR-0095 name shadow at the root**:
the pin node is now honestly ported, and the `--unport` correction every read since SET-AF2 needed is
retired. Both touched hubs were legacy and were migrated in the same touch (§6), and the new proof
module is 0-importer, so the order is one manager lane plus one worker order
([automorphicForm/WORKORDER-AF5-rightconv-regularity.md](automorphicForm/WORKORDER-AF5-rightconv-regularity.md)).
Measured after the manager's layer: `needed` **899 / 370,921**, the AF shelf 42 / 20,957 ready and
80 / 16,549 leaves. W1 then landed in one worker order — `Adelic/RightConvRegularity.lean`, 530 lines,
checker 1 ok / 0 / 0, silent 5.6 s, **no mathlib rename needed**, and one measured deviation
(`AdeleRing` is a semireducible `def`, so `unipotentGL2_coe` cannot key a `rw` at that type; FR-0105).
Measured after W1, and the brief's forecast was exact to the line: `needed` **898 / 370,450**, the AF
shelf **42 / 24,319** ready with 80 / 16,549 leaves, `--selfcheck` PASS — with **no `--unport`
correction anywhere**. That leaves the archimedean-derivative chain (8 leaves / 1,510 silo / 1,001 net)
with its two headline rows ready as the column's next set. Its §1.5/§1.6 record the two landings and
§8 the two re-reads.

The sixth is **landed** (2026-11-02):
[automorphicForm/SET-AF6.md](automorphicForm/SET-AF6.md), **differentiating the right-convolution
operator along an archimedean flow** — the two triple-conjunction headlines
(`archDerivAt{,Complex}_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn`, 1,246 + 1,248 silo) that
SET-AF5's translation law was written for. The set has no definition gate (both rows are gate-free at
the declaration level), so its manager's layer is the **largest promotion the column has made**: the
port held the pin's **left**-derivative half of the archimedean chart `private` on the `Reserve` shelf,
cut there on 2026-10-23 because the *right* headline never reaches a left derivative — and these two
rows are the consumer its own header predicted ("a consumer that needs the left action has to promote").
It is now two live public modules,
`Adelic/FactorizableTestFnArchSmooth{,Complex}Left.lean` (593 + 594 lines, 72 public declarations
each), with the **nine** declarations an earlier cut had lost restored from the pin (the four real
and five complex ones `CARRY-FORWARD.md` had recorded as having no home — that entry is now resolved).
The two `Reserve` shelves are deleted, the two live modules' headers repointed, and the register grew
112 → 114 modules / 3,474 → 3,618 public declarations. Measured effect on the order: **66 of each
file's 113 prelude declarations (491 of 1,246 pin lines) become imports**, leaving 47 declarations /
694 lines to transcribe per file — and because the promotion renames the declarations to the port's
content names, it does **not** move the shelf figure (`needed` is 898 / 370,450 before and after): a
promotion's payoff is the order's size, never the read. The set is 2,494 silo / ≈985 net, one worker
order, R2 being R1 by the vocabulary map
([automorphicForm/WORKORDER-AF6-archderiv-rightconv.md](automorphicForm/WORKORDER-AF6-archderiv-rightconv.md));
its §8 carries the re-read. Both proof bodies then landed in one worker order — `ArchDerivRightConv.lean`
(802) and `ArchDerivRightConvComplex.lean` (808), 41 `private` + 1 headline each, checker 2 ok / 0 / 0,
silent 7.0 s and 16 s, R2 compiled first try by the pin's vocabulary map, and the promotion's 72 imported
declarations needed **0** local re-statements. Measured after the landing: `needed` **896 / 367,956**
(exact), the frontier 1,519 / 759,410 (exact), and the `AutomorphicForm` shelf **42 / 22,818** — one row
and 779 silo more than forecast, because the set readied a row whose missing premises were *both* of its
rows and a per-row return cannot see that (FR-0106). That row is
`archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt` (779) — the archDeriv↔Casimir
bridge, and the natural headline of SET-AF7, which is the eight remaining leaves of the family.

The seventh **is landed** (2026-11-02) and it is the column's experiment in *strategy*:
[automorphicForm/SET-AF7.md](automorphicForm/SET-AF7.md), the cone's largest node
`bigCell_eq_sum_pureTensor_of_flat_family` — **5,407 silo, 4,753 net, 458 declarations** (457 of them
`private`) — ported **mechanically** rather than by selection: one module, the pin's text at the pin's
own inner namespaces, the tooling translated (`p2m_open` → `open`/`open scoped`, `p2m_export`/
`p2m_reactivate` dropped, `attribute [-…]` shims dropped). The measurement the strategy was chosen on:
a full elaboration pass is **17 s** for 5,445 lines (~320 lines/s, *cheaper per line* than the
column's 1,200-line modules), and the mechanical pass left only **16 sites** — all v4.34 drift, none a
statement change. Landed: `Adelic/BigCellExpansion.lean`, 5,445 lines, 1 public + 463 `private`,
checker **1 ok / 0 / 0**, axioms clean, **zero warnings**, consumer probe 0 errors; `dedup --cross`
found 31 clusters (3 fixed by FR-0101 — the pin's `placeBorel`/`placeBorelSpace`/`infMS` are the
port's `M4aS4.*` verbatim — 28 kept with reasons), and `move_dead` shelved **12 declarations / 150
lines** of the pin's abandoned real-place Fourier route to
`Reserve/AutomorphicForm/Adelic/BigCellExpansionDead.lean` (1,749 lines with the 118 premises).
Measured after the landing: `needed` **895 / 362,549** (−5,407, exact), frontier 1,520 / 764,817, the
AF shelf 41 / 17,411. Its 31 cross-dedup clusters were then **shared, not just re-triaged** (§5.1): 25 were true duplicates
— 13 `ArchKFiniteFamily.LevelInvariance` engine lemmas promoted in place to public (which also took
that module from 1 to **14 checker-verified** declarations) and 12 `InducedSectionFlat` ones already
public — so the module went **5,445 → 5,176 lines** and 31 → 6 clusters; the 6 that stayed are
trivial (`rTrans`, 3 lines) or **provably non-substituting** (binder/call-site mismatch, each tested by
substitution and reverted), which is FR-0111's measured 20% `shape`-tier false-positive rate. Two tool
frictions came out of the set: FR-0110 (`move_dead`'s scanner dropped capital Greek names —
**fixed** this session) and the standing FR-0104 (attribute-only references).
Its §5 is the execution record; the queued eighth set is the *composition* counter-example (§A8). The
landing's dead tail (6 declarations / 109 lines per module, all dead in the pin as well) was triaged
rather than carried (§1.7): `l5_continuous_rightConv` **deleted** — it is the first conjunct of AF5's
public headline, so a duplicate — and the other five **shelved** into
`Reserve/AutomorphicForm/Adelic/ArchDerivRightConv{,Complex}Dead.lean` (172 + 173 lines, 8 declarations
each with the premises they need), leaving both live modules at 0 dead.

The eighth **is landed** (2026-11-02) and it is the composition counter-example to the seventh:
[automorphicForm/SET-AF8.md](automorphicForm/SET-AF8.md),
`rightConv_rightTranslate_mem_of_isCuspSubrep` — 3,833 silo of which **3,015 lines were already in the
port**, so the set is 11 declarations / ≈600 pin lines of work, not the 50 / 837 a name-anchored
reading suggested. Its manager's layer is the wave's real content: the `Def_` gate measured at **0
missing** (`gate_scan` over the wrapper and four `Def_` modules), the pin's generic convolution-operator
block homed into `RepTheory/ConvolutionLimit.lean` (`ConvTransport`, 8 declarations, checker 32 ok), two
promotions in `TestFnTop` (which also migrated that module off the frozen checker: 3 ok), a module
skeleton with the pins' `JoinOfFamilies` block, and a `#check` surface probe that verified ~90 imported
names before the worker started — and which, per FR-0112, could not see the one thing the proofs
actually needed (a scoped `ArchInfra` instance). Landed: `Cusp/RightConvSubrep.lean` (471 lines, 1 ok /
0 / 0), `integral_mul_dconvWith` in the engine (884 lines, 33 ok / 0 / 0), consumer zone 0 errors. The
re-read is exact: `needed` **894 / 358,716**, frontier 1,521 / 768,650, the AF shelf **40 / 13,578**,
nothing readied (return 0) — and it produced FR-0114: a `spec-pin:` wire on a *skeleton* marks the
whole pin file ported, so a shelf read taken mid-dispatch must `--unport` the in-flight rows.

The ninth is **scoped, its manager layer landed, and dispatched** (2026-11-02):
[automorphicForm/SET-AF9.md](automorphicForm/SET-AF9.md), the set SET-AF6 §9 deferred by name — the
**archimedean derivative algebra** (`[E, F⁻]` commutators, the character identities, the row-isometry
invariance — 8 leaves / 1,510 silo) and the **two Casimir rows** it is the bridge into (993 silo; the
779-line `archCasimirAt_rightConv_of_…` is the headline SET-AF6 §9 pointed at). **10 rows / 2,503
silo, ≈1,380 lines / 105 declarations of work** (three instruments agree to 2%, and SET-AF6's forecast
1,001 net agrees with order A's 975 to 2.6%). It is the second composition set in a row — 911 of its
2,281 declaration lines are already in the port — and it has **no `Def_` node** (6 modules, 0 missing).
Its homes are the modules that already hold the engines the leaves extend
(`ArchCasimir{,Complex}.lean`, 0 importers each), and the legacy tax there was measured **at one
hypothesis**: the migration landed at **131 ok / 0 mismatch / 0 missing** and **97 ok / 0 / 0** (the
drift was `smooth_sub`'s binder spelled `_hθ`), both modules out of `PORT_FILES`, register 114 → 112.
The two rows go into `ArchDerivRightConv.lean`, which gained the four imports their statements need and
still checks 1 ok. Two orders in one dispatch, sequenced (they share the `ArchCasimir` hub): A = the
algebra (975), B = the bridge (405); the manager also left three surface probes, one of which states
both order-B headlines as `example`s and elaborates them.

**Landed** in one dispatch: `ArchCasimir.lean` 1,640 lines, `…/ArchCasimirComplex.lean` 1,588,
`…/ArchDerivRightConv.lean` 1,167, and a 60-line consumer zone — ≈1,529 written lines / 103
declarations (10 public headlines + 93 private helpers), every file silent, zero warnings, all ten
headlines on `[propext, Classical.choice, Quot.sound]`, `dedup --within` 0 and `move_dead` 0 after one
deleted `rfl` restatement. The checker owns all three at **135 / 101 / 3 ok, 0 mismatch / 0 missing**.
This is also the set that retired the last in-source `-- pin:` markers: 282 lines stripped from the two
Casimir modules and the wires widened 3 → 7 and 1 → 5 instead, because a marker was also naming the pin
file its declaration came from — the strip and the wire are one edit (playbook §5). Two Appendix-B rows
turned out to be deletions (`dirM` ≡ `archDirMatrixComplex`; `CasLeft2.Ld` ≡ `CommConv17.Lf`, the pin's
own cross-file duplicate), and **eight** "already in the port" declarations had to be re-stated
privately because their port copies sit *downstream* of the home (`TSRot.*` in
`Cusp/CutWeightDecomposition.lean`) — FR-0115. The re-read: `needed` **884 / 356,213** (−10 / −2,503,
exact), frontier 1,531 / 771,153, the AF shelf **45 / 14,152** — the two rows left and **seven rows were
readied**, not the 0–1 the brief predicted (FR-0106's multi-premise effect at full strength).


The tenth is **scoped, its wires landed, and dispatched** (2026-11-02):
[automorphicForm/SET-AF10.md](automorphicForm/SET-AF10.md), the **complex Casimir algebra** — the
seven rows SET-AF9 readied, taken as the shelf's own reply to that landing (five of them import only
`Definitions/` plus AF9's complex commutator headline, and four open by destructuring its fifteen-fold
conjunction positionally). **7 rows / 1,567 silo / 570 lines to write in 27 declarations**: 915 of its
1,485 declaration lines are already in the port, one row carries 289 of the work in a 21-declaration
prelude, and the other six are one `solution` each. Third set in a row with **no `Def_` node** (six
modules, 0 missing), no legacy migration, no promotion, no new module and no new import: the homes are
`ArchCasimirComplex.lean` (5 rows, wire 5 → 10) and `ArchDerivRightConv.lean` (2 rows, wire 4 → 6), and
the manager's whole layer is **7 `spec-pin:` lines** (landed: both modules re-check 101 and 3 ok,
0 mismatch / 0 missing) plus a statements probe that states all seven headlines as `example`s and
elaborates — no per-declaration markers (playbook §5). One order; it is below the recipe's 1,100–1,400-line band and the brief says so, taking it as its own set
because the engine, the homes and the wires already exist. Named next: the Whittaker/Casimir ODE
quartet (4 leaves / 1,744 silo), a different subject, measured so the next pass starts from the number.

**Landed** in one dispatch: `ArchCasimirComplex.lean` 2,127 lines and `…/ArchDerivRightConv.lean`
1,291, 27 declarations (7 public headlines + 20 private helpers), both files silent, zero warnings, all
seven headlines on `[propext, Classical.choice, Quot.sound]`, checker **106 / 5 ok, 0 mismatch / 0
missing**, `dedup --within` 0 and `move_dead` 0 on both. The re-read: `needed` **877 / 354,646**
(−7 / −1,567, exact), frontier 1,538 / 772,720, the AF shelf **39 / 12,906** — and the return was
**one** row (`archCasimirAtComplex_rightConv_of_…`, 321) against AF9's seven, which is the sign
difference FR-0106 predicted: AF10's rows sat at the end of a chain whose premises were already ported.
Two side findings: FR-0115 recurred for 10 lines (two helpers whose port copies live in
`ArchCasimir.lean`), and the manager's attempt to apply the dedup rule to them — import the home,
delete the copies — was **reverted**, because that "home" is the pin's *transcription namespace*
(`Elem17LR`, `OsAlg17`) and the import does not resolve the unqualified names; that is FR-0116.

The eleventh **is scoped, not dispatched** (2026-11-02):
[automorphicForm/SET-AF11.md](automorphicForm/SET-AF11.md), the **Whittaker coefficient's API and its
archimedean differentiability** — the column's return to the recipe's cheapest cut after four
composition sets. **9 rows / 1,595 silo / 1,211 net (`port_plan`), 1,267 lines in 49 declarations**: the
transformation law under the unipotent (95 lines, **54 project consumers**), additivity over a locally
constant coefficient, continuity, the diagonal reduction, shell surgery on the `diagOne` value, the two
realization-scalar identities, and the two differentiability rows along the archimedean flow (real and
complex). Only **146 of 1,413 declaration lines are in the port** — this is a *transcription* set in the
AF7 sense, chosen on fan-in (17/54, 10/17, 3/14, 4/12), which is SET 3's cheap-leaf signal. Fourth set
in a row with **no `Def_` node** (five modules, 0 missing); the home is the object's own module,
`Adelic/WhittakerCoefficient.lean` (82 lines, legacy), whose migration is measured at **one `spec-pin:`
line → 8 ok / 0 mismatch / 0 missing**, and which gains three imports (the two arch Casimir modules
and `AdelicTraceFin`) for the analytic and trace rows. Named next: the **local Casimir ODE pair**
(`gl2Complex_whittaker_system_…` 695 / 650 in 52 declarations, `gl2Real_whittaker_ode_…` 347 / 315 in 10
— 1,042 silo / 965 net), the *local* side of the same object, solved with explicit special functions.

The twentieth **is landed** (2026-11-07): [automorphicForm/SET-AF20.md](automorphicForm/SET-AF20.md),
the **rational unipotent Haar measures** — the block `SET-AF4 §9` measured and `SET-AF5 §7` call 7
deferred to "SET-AF6", which six sets then walked past because its read owed a price on the
`RationalCentreUnipotentQuotient` definition gate. That gate is four pin `Def_` role modules /
19 declarations / **no proofs**, and paying it is the set's manager layer:
`MeasureTheory/HaarQuotient.lean` (3 ok — a mathlib supplement, generic over an arbitrary group, with
the negative recorded: mathlib has only the fundamental-domain quotient measure) and
`AutomorphicForm/Adelic/UnipotentQuotient.lean` (16 ok — the pin's three chained `Def_` modules, one
module because they are one subject). The five rows are **5 / 1,154 silo / 990 net in 95 declarations**,
and **four of the five were never on the shelf**: they are one edge behind the `NumberField` leaf
`finite_setOf_algebraMap_mem_of_isCompact` — the recipe's SET-10 shape. The leaf is also the shelf's
best buy by return (**123 silo → 2,113**, the whole point of reading leaves), and it is what makes
the set a cut at all: SET-AF19 §8 had named the 3,248-silo `diagOne` family as its successor, and
measuring that family's return gives **zero** (FR-0144). Three orders over three new modules, no
insertion, no legacy module: `NumberTheory/AdelicDiscreteness.lean` (7 ok), `…/RationalUnipotentClosed.lean`
(17 ok) and `…/RationalUnipotentHaar.lean` (62 ok / 8 own — the pin's eight `scoped instance`s are
public theorems, and the corpus cannot index a `scoped instance`, so they are `own:` rows in
`decl_markers.tsv`). Landed in one dispatch: 1,068 source lines / 94 declarations, every module
silent and zero-warning, all five headlines on `[propext, Classical.choice, Quot.sound]`, `dedup` 1
cluster (the pin's own `_impl` ≡ headline) and 0 dead, three consumer zones at 0 errors. The re-read
is exact: `needed` **818 / 341,853 → 813 / 340,699**, the AF shelf **32 / 13,111 → 34 / 14,193** with
the two forecast rows readied (635 + 447), and the `AutomorphicForm` demand 322 / 140,337 →
318 / 139,306. Named next, priced while the orders ran: the **box-sheet fundamental-domain pair +
the quotient identity** (`isFundamentalDomain_boxSheet_rational{Torus,Centre}Unipotent` 440 + 340,
`integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient` 366)
— 3 rows / 1,146 silo / **931 net in 78 declaration groups**, of which 71 lines are already in the
port because this set's module supplies them, i.e. a composition set with one promotion
(`countable_numberField`).


The twenty-first **is landed** (2026-11-07):
[automorphicForm/SET-AF21.md](automorphicForm/SET-AF21.md), the **rational unipotent quotient
measures** — the continuation SET-AF20 §9 forecast, one level deeper into the same block: the
**box sheets** (the box read inside each subgroup, as a fundamental domain for the image of the
Borel), the **Haar-quotient integral calculus** (`∫_S f = ∫_q ∫_T f (· * q.out)` for `Γ ≤ H`, in
both `ℝ≥0∞` and `ℂ` forms), and the **comparison identity** that identifies the torus-unipotent
quotient integral with the centre-unipotent one after summing over `Kˣ`. Eight rows / 2,352 silo, of
which only two were shelf leaves — the other six were one to three edges behind them, found by the
gateway query. **1,342 net in 101 declarations**, and 739 of the 1,160 AF declaration lines were
already in the port: this is the column's most composition-heavy set since AF8/AF9, composed of the
module AF20 had just written (`ratCentralHom`, `sheet`, `sheet_entries`, `exists_eq`, …). Four
orders over two new modules and one insertion, no definition gate, no legacy module, no promotion:
`MeasureTheory/IsFundamentalDomainCosets.lean` (216 lines, 6 ok — a mathlib supplement with the
negative recorded), `AutomorphicForm/Adelic/RationalUnipotentBoxSheet.lean` (720, 28 ok),
`MeasureTheory/HaarQuotient.lean` (100 → 955, 5 ok — the supplement module AF20 created, gaining its
44-declaration private engine and two headlines) and
`…/RationalUnipotentQuotientIntegral.lean` (317, 13 ok). Landed in one dispatch: every module silent
and zero-warning, all eight headlines on `[propext, Classical.choice, Quot.sound]`, `dedup` 0 and
`move_dead` 0 on all four, four consumer zones at 0 errors. The re-read is exact: `needed`
**813 / 340,699 → 805 / 338,347**, the frontier 1,603 / 786,677 → 1,611 / 789,029, the `HaarQuotient`
demand 2,245 → 1,323, and **no row readied** (as forecast: the next block up needs four more rows).
Named next: the **arch-approximation gate leaves** — seven premise-free rows / 591 silo / **476 net
in 20 declarations** that ready ≈4,653 silo (`exists_isRightEquivariant_comp_subtype_eq_of_injective`
70 → 1,445, `isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous` 71 → 1,361,
`isFactorizableTestFn_sum_mul_comp_mul_mul` 98 → 1,131, and the `IsKfSmooth`/lift string). That is
the column's cheapest readiness event and AF22.


The twenty-second **is landed** (2026-11-07): [automorphicForm/SET-AF22.md](automorphicForm/SET-AF22.md),
the **archimedean approximation's cheap gates** — a *portfolio* set, chosen on the recipe's §1 return
measure rather than on subject: six premise-free rows / 392 silo / **201 net in 19 declarations** that
ready **4,438 silo** (1,445 + 1,361 + 1,131 + 260 + 133 + 108). Three new modules, no insertion, no
`Def_` gate: `Adelic/TestFnInvariance.lean` (243 lines, 10 ok — the factorizable-test-function algebra
and the generic right-equivariant extension lemma), `Adelic/LevelCompactness.lean` (149, 6 ok — smooth
vectors have a finite orbit under a compact, and `levelOne ⊓ finiteAdelicGL2Subgroup` is compact) and
`Adelic/LsXiCharacter.lean` (105, 3 ok — the character of a continuous non-vanishing `LsXi` function is
trivial on the principal idèles and continuous). Landed in one dispatch: every module silent and
zero-warning, six headlines on `[propext, Classical.choice, Quot.sound]`, `dedup` 0 and `move_dead` 0,
three consumer zones at 0 errors. The re-read is exact: `needed` **805 / 338,347 → 799 / 337,955**, the
ready shelf **62 / 20,332 → 70 / 24,770** with **the eight rows these gates were taken for** — the
1,175 archimedean approximation identity, the 1,131 cut projector, the 1,361 LsXi bound, and their five
companions — and the `AutomorphicForm` demand 314 / 138,052 → 308 / 137,660. Its two carried findings
are checker-side: the statement hash is syntactic in a binder's *name*, in a section variable vs an
inline binder, and in a *qualified* name (FR-0145), and `open scoped Classical` is load-bearing in the
`ContDiff` elaboration of the entry space. Named next and **landed the same day**: SET-AF23, the
archimedean cut projector's two headlines plus the two membership lemmas they consume (4 rows / 2,576
silo / 1,342 net, 45 % of it already in the port).


The twenty-third **is landed** (2026-11-07): [automorphicForm/SET-AF23.md](automorphicForm/SET-AF23.md),
the **archimedean cut projector and the archimedean approximation** — the two rows SET-AF22's gate
leaves were readied *for*, taken together with the two membership lemmas they consume so that the
column does not pay for gates and leave the door shut. 4 rows / 2,576 silo / **1,342 net**, of which
1,148 declaration lines were already in the port: `Adelic/ArchApproximation.lean`, 1,229 lines and 49
declarations, checker **7 ok / 0 / 0**, axioms clean, silent, `dedup` 0, `move_dead` 1 (a helper dead
in the pin too, kept for parity), consumer 0 errors. The set is the best evidence yet for the
composition pricing: **only ~1,090 of its 2,576 silo lines were new** — row 3's 1,175 pin lines were
~90 % `RepTheory/ConvolutionLimit.lean`'s `dconvWith` engine plus `ArchApproxIdentity/ArchInfra.lean`'s
row-isometry topology, and row 4 was assembled from `ArchCompactOrbit`/`ArchCutProjector`/
`ArchDualCut`/`ArchCutSpan`. The re-read is exact: `needed` **799 / 337,955 → 795 / 335,379**, frontier
1,617 / 789,421 → 1,621 / 791,997, and the ready shelf **70 / 24,770 → 72 / 24,200** — the four taken
rows left and **six** successors entered, one more than the per-row return column predicted (FR-0106's
multi-premise effect, again). With it, the archimedean cut projector is usable, which is what the
isotypic/`CuspidalConstituent` block is written against.


The twenty-fourth **is landed** (2026-11-07): [automorphicForm/SET-AF24.md](automorphicForm/SET-AF24.md),
the **`𝔰𝔩₂`-string decomposition at a complex place** — the `su(2)`/circle-weight block SET-AF23 §5
named by hand, taken as four rows over two new modules. Three headlines (the three complex
derivatives preserve an archimedean-smooth finite-dimensional `Y` and the flows `iH`/`rotR`/`rotS`
differentiate it; `Y` has a basis of `𝔰𝔩₂` strings with circle weights; a vector killed by all three
is of trivial archimedean character) and the coordinate-matrix engine for a rotation-stable span.
4 rows / 2,016 silo / **1,314 net in 88 declaration groups**, of which **575 lines are one prelude
the pin copies byte-identically into two files** (measured: the two 253-line blocks differ only in
their namespace label) — so this set's dedup saving was the whole block, written once publicly at the
pin's names. No definition gate (five `Def_` modules, 0 missing), no insertion, no legacy module; one
promotion: `apply_mul_archFlowAtComplex_eq` was `private` in `ArchCasimirComplex.lean` while the pin
states it publicly in two files, so it is public at the pin's name (**106 → 107 ok**, 12 s rebuild,
dependent cascade 3 modules / 1,016 lines). Landed in one dispatch, two orders on disjoint files:
`Adelic/Su2Strings.lean` (**1,207 lines, 81 ok / 0 / 0**) and `Adelic/ArchRotCoordinate.lean`
(223 lines, 3 ok / 0 / 0), both silent and zero-warning, all four headlines on
`[propext, Classical.choice, Quot.sound]`, `dedup --within` 0 and `move_dead` 0, two consumer zones
at 0 errors. The re-read: `needed` **795 / 335,379 → 791 / 333,363** (−4 nodes / −2,016 lines, the
line figure exact), literal 807 / 338,844 → 803 / 336,828, frontier 1,621 / 791,997 → 1,625 / 794,013,
ready block **untouched at 72 / 24,200**, leaves 212 / 55,301 → 210 / 54,362, `AutomorphicForm`
demand 304 / 135,084 → 300 / 133,068. Two carried lessons. **Two of the set's four rows were on
neither block** — 908 and 169 sit one edge behind the leaf 755, so the shelf omits them and only
`af-return.py` prices them; the brief's first forecast had priced 1,077 silo out of a ready block that
never held it, and a row named in another set's prose is not a row on the shelf (FR-0150). And a set
of *n* rows removes **n** nodes from `needed`, not n/2 — the line column was exact, the node column
was not. The 458-line `exists_eq_sum_su2String_highestWeight` row that this set moves to two premises
short is **not** the next set: its closure is 107 nodes / 29,103 silo (it drags the whole
Siegel/LsXi/Petersson block), so it is a chain head, not a gate. Named next by the return column: the
**cuspidal-lift carrier operator**, `CuspidalSpectrum.exists_isLift_rightConv` (199 silo, in-degree
11, readies 4 rows / 1,055) — AF25.


The twenty-fifth **is landed** (2026-11-07): [automorphicForm/SET-AF25.md](automorphicForm/SET-AF25.md),
the **cuspidal lift of a convolution operator and its commutation** — the head of the column's return
column after AF24, taken as the gate *and* its door: `CuspidalSpectrum.exists_isLift_rightConv` (199
silo, in-degree 11) readies four rows / 1,055, and all four are in the set. The subject is one
construction (the bounded lift of a function-level operator to the cuspidal carrier) and the four
commutation statements that make it an operator of the level-`N` Hecke algebra, plus the `K`-finite
companion (`IsCuspSubrep` of a closed cusp subrepresentation). 5 rows / 1,254 silo / **1,108 net in 19
declaration groups**, one new module, no definition gate. Landed in one dispatch:
`Adelic/Cusp/SpectrumLift.lean`, **1,278 lines, 19 ok / 0 / 0**, silent, zero warnings, all five
headlines on `[propext, Classical.choice, Quot.sound]`, `dedup --within` 0 and `move_dead` 0, consumer
at 0 errors. Its carried finding is a *composition* dividend: the coset-sum prelude's
`cuspInvSubcarrier` is the compact-open-`U` twin of the landed `cuspLevelSubcarrier`, and its 237-line
orthogonal-vanishing lemma has no port counterpart — so the level analogue still on the shelf
(`apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_…`, 260) is now a specialisation of mathematics
this set wrote in general. The re-read is **exact on all six forecast figures**: `needed`
**791 / 333,363 → 786 / 332,109**, literal 803 / 336,828 → 798 / 335,574, frontier 1,625 / 794,013 →
1,630 / 795,267, ready **72 / 24,200 → 71 / 24,001**, leaves unchanged at 210 / 54,362,
`AutomorphicForm` demand 300 / 133,068 → 295 / 131,814, no rows readied (the door was taken with the
gate). Named next and **scoped**: AF26 is the **LsXi/Petersson bound pair** (1,361 + 447, 1,808 silo /
1,665 net), not the compact-operator block — that block's gateway needs seven unported premises, two of
which are this pair, so the chain is AF26 → AF27.


The twenty-sixth **is landed** (2026-11-07): [automorphicForm/SET-AF26.md](automorphicForm/SET-AF26.md),
the **local `L²` bound of an `LsXi` function** — the pair
`exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre`
(1,361) and its `…_of_isFundamentalDomain` sibling (447): the bound that turns the Siegel covering
theorem into an `L²` estimate, and the ready half of the compact-operator chain. 2 rows / 1,808 silo /
**1,665 net in 120 declaration groups**, both on the ready block, sharing **no** declaration — two
independent transcribing jobs in one module (`Adelic/LsXiBound.lean`, **1,843 lines, 2 ok / 0 / 0**,
101 + 27 private helpers, which is exactly the pin's own surface: its `S_` files are 92 + 9 private and
25 private over one `solution` each). Silent, both axioms clean, consumer 0 errors; the one `dedup`
cluster is the pin's headline-vs-engine split and `move_dead`'s 11 declarations are the pin's own text
(no `--expose`). The re-read is exact on all six figures: `needed` **786 / 332,109 → 784 / 330,301**,
literal 798 / 335,574 → 796 / 333,766, frontier 1,630 / 795,267 → 1,632 / 797,075, ready
**71 / 24,001 → 69 / 22,193**, leaves unchanged, `AutomorphicForm` demand 295 / 131,814 → 293 / 130,006,
no rows readied. Its §6 names AF27 as the `L²`-continuity trio.

The twenty-seventh **is landed** (2026-11-07): [automorphicForm/SET-AF27.md](automorphicForm/SET-AF27.md),
the **`L²`-continuity of right convolution** — the smallest set of the column and its most
composition-heavy: 3 rows / 426 silo / **79 net in 7 declaration groups**, of which 297 of the 376
declaration lines were already in the port. `Adelic/RightConvLpContinuity.lean` (459 lines, **6 ok /
0 / 0**, silent, axioms clean, `dedup` 0, `move_dead` 0, consumer 0 errors) holds the Young/Hölder
bound (pin 78, transcribed by the manager), the uniform `L²`-continuity of the convolution orbit
(pin 209) and the Arzelà–Ascoli lemma behind its covering step (pin 139, generic). The set removes
**three of the six** premises the compact-operator gateway
`isCompactOperator_lift_rightConv_comp_cuspSubcarrier` (285) is missing — for 426 silo. One honest
statement deviation: the pin's `eLpNorm_two_eq` is *false* at mathlib v4.34 (`eLpNorm` is `∞` off
a.e.-strong measurability), so the port's copy is `private` and carries the measurability hypothesis,
which keeps it out of the checker's diff. The re-read is exact on five of six rows — `needed`
**784 / 330,301 → 781 / 329,875**, literal 796 / 333,766 → 793 / 333,340, frontier 1,632 / 797,075 →
1,635 / 797,501, ready unchanged at 69 / 22,193, leaves 210 / 54,362 → 208 / 54,145 — and the sixth
(`AutomorphicForm` demand) is off by one node because the generic row leaves the `MeasureTheory`
namespace, not `AutomorphicForm.`'s: 293 / 130,006 → **291 / 129,719**, with `MeasureTheory`
15 / 2,120 → 14 / 1,981.

**The three sets together**: AF24's `𝔰𝔩₂`-string block (1,314 net), AF25's cuspidal lift (1,108 net)
and AF26's LsXi bound (1,665 net) plus AF27's continuity trio (79 net) took `needed` from
**795 / 335,379 to 781 / 329,875** (−14 nodes / −5,504 lines) over four new modules and one promotion,
with every re-read exact on lines. **The largest remaining subject is the Weyl intertwining pair**
(1,349 + 1,291, 2,640 silo but only 1,072 net); it could not be scaffolded verbatim because the pin
qualifies `NumberField.AdelicBox.integralFiniteAdeles` (the port homes it in `AdelicLevel`) and one
hypothesis uses an auto-bound binder that the project-wide `autoImplicit false` forbids — two
one-line **manager** decisions recorded as FR-0151, which is where the next pass starts.


The twenty-eighth **is landed** (2026-11-07): [automorphicForm/SET-AF28.md](automorphicForm/SET-AF28.md),
the **left Casimir on factorizable test functions** — `Ω α` is again factorizable and arch-bi-finite,
right convolution by `Ω α` is the Casimir of the convolution, and the level/arch-cut memberships hold;
the real and complex places, plus the eigenvalue transfer (an arch-cut eigenvector of
`rightConv · f` is one of `rightConv · f'` for an arch-bi-finite `f'`). 3 rows / 1,535 silo / **1,338
net in 95 declaration groups**, one new module `Adelic/LeftCasimirTestFn.lean` (**1,174 lines, 81
ok / 0 / 0**), the pin's cross-file block written once (14 declarations shared by the real and complex
places). The set's one route change is its best: the eigenvalue headline does **not** replay the pin's
290-line `sandwich` — the port's `ArchApproxIdentity.integral_mul_dconvWith` *is* that sandwich's
conclusion — so the pin's `set_option maxHeartbeats 3200000` disappears and the module fits the default
200,000 budget. The re-read: `needed` **781 / 329,875 → 778 / 328,340**, frontier 1,635 → 1,638, ready
69 → 66, no rows readied.

The twenty-ninth **is landed** (2026-11-07): [automorphicForm/SET-AF29.md](automorphicForm/SET-AF29.md),
the **Whittaker coefficient at `diagOne`** — the circle-weight identity against the split torus, and the
cusp-constituent expansion in two normalizations. 3 rows / 2,343 silo / **1,539 net**, of which 563 were
one prelude the pin copies into two files: the two `CuspidalConstituent` `S_` files are byte-identical
over lines 1–574 except their `namespace` line, and their proofs differ in exactly one `refine` conjunct
(the normalized row keeps one more conjunct), so the second row is the first with that line changed.
Its manager layer is a **`Def_` port**: the 913 row names
`NumberField.AdeleRing.infiniteUnitsComponent`, which the port had never carried, so it was added at the
pin's name in `NumberField/NumberField/FiniteIdeles.lean` with its `rfl` lemma (module 3 ok → 5 ok).
Landed as `Adelic/WhittakerDiagOne.lean` (**1,865 lines, 97 ok / 0 / 0**), one `dedup` cluster pair that
is the pin's own per-file duplication. Re-read: **778 / 328,340 → 775 / 325,997**.

The thirtieth **is landed** (2026-11-07): [automorphicForm/SET-AF30.md](automorphicForm/SET-AF30.md),
the **centre-cut Siegel set as a cover modulo the centre** — the ample cover, its `u = 0` non-vacuity,
the finite `L²` mass of the union, and the flat conjugation-invariant test factor. 4 rows / 2,203 silo /
**1,737 net in 166 declaration groups**; `Adelic/Siegel/CentreCutCover.lean`, **1,961 lines**, landing at
**143 ok / 0 / 0** — the column's largest checked surface for a set. Two findings. The 346-line
`not_coversModCentre…of_eq_zero` row is a **one-line proof** (its whole engine is already public at
`Cusp/CentreCutEngine.lean:417-749`, ported from a sibling `S_` file) — the cheapest row landed so far;
and the 905-line test-factor row is genuinely new (`BumpAux`: `Real.smoothTransition`, the Hilbert–Schmidt
distance to the identity, the `1/16` threshold forcing `U = {det ≠ 0}`, the determinant weight, the
flatness identity). **This set also produced the round's main review finding (FR-0152/0153)**: the worker
landed 128 helpers `private` on a sibling module's precedent while the pin states them publicly, so the
checker read 5 ok for a module holding ~140 pin declarations; the promotion experiment took it to 143 ok
with nothing private, and the single `MISMATCH` it exposed was cured by dropping an *unused* `open` from
the module header rather than by privatising the declaration. Re-read: **775 / 325,997 →
771 / 323,794**.

The thirty-first **is landed** (2026-11-07): [automorphicForm/SET-AF31.md](automorphicForm/SET-AF31.md),
the **determinant-window cover and the archimedean unit's strict contraction** — cut on the return column
(136 silo readies 871, ratio 6.4, the shelf's last leader) as a gate-and-door pair. 2 rows / 1,007 silo /
**746 net**; `Adelic/Siegel/DetWindowCover.lean`, **1,058 lines, 53 ok / 0 / 0**, surface faithful from
the start (the pin's 51 helpers public, 5 port-local `private`). The door does **not** in fact reuse
SET-AF26's `∫⁻` bound — its finiteness is five lines from its own `hL2` and its non-vanishing is the
pin's 178-line open-set positivity lemma — so four imports of the scaffold turned out idle and were
removed. Carried item: the pin's four shared helpers exist in the port only as `private` copies in five
modules, which is the next dedup pass's first job.

The thirty-second **is landed** (2026-11-07): [automorphicForm/SET-AF32.md](automorphicForm/SET-AF32.md),
the **archimedean type lattice and the isotypic cusp submodule** — the type-submodule interpolation, the
pointwise isotypic predicate from isotypic-submodule membership (**27 project consumers**, the shelf's
fan-in leader), the inf/sup exchange for the `τ`-isotypic parts, and the arch test factor's character
twist. 4 rows / 1,128 silo / **1,005 net in 68 declaration groups**; `Adelic/IsotypicArchType.lean`,
**1,148 lines, 34 ok / 0 / 0** after the surface gate again (4 → 34, no `MISMATCH`, 33 declarations
left private with a reason each: 30 pin-private, 2 port-only extractions, 1 the pin's `scoped instance`
that the statement corpus cannot index). The hardest row was 214, and the difficulty is the port's own:
compactness of the row-isometry group is a `scoped instance` in `ArchCompactOrbit`, so the pin's
`haveI : CompactSpace` cannot be transcribed and its `haveI := hSfd` walls pass hypotheses into instance
search — the one place `have` and `let` differ at v4.34.

**The six sets together** (AF27–AF32): `needed` **781 / 329,875 → 765 / 321,659** (−16 nodes / −8,216
lines, matching the sets' silo to the line), frontier 1,635 / 797,501 → 1,651 / 805,717, ready
69 / 22,193 → 62 / 16,628, leaves 204 / 52,711, `AutomorphicForm` demand 275 / 121,503. Five new modules
and one `Def_` port; every set's re-read exact on lines. The largest subject left is still the **Weyl
intertwining pair** (1,349 + 1,291: 2,640 silo / 1,072 net), blocked on the two statement-spelling
decisions of FR-0151, and the **isCuspConstituent cluster** (94 nodes / 21,595 silo).


The thirty-third **is landed** (2026-11-07): [automorphicForm/SET-AF33.md](automorphicForm/SET-AF33.md),
the **Weyl intertwining pair** — the set SET-AF27 §7 had written off as blocked on two statement-spelling
"conflicts" (FR-0151). **Both were scaffolding errors**: the qualified
`NumberField.AdelicBox.integralFiniteAdeles` exists (in `TateGlobal/IdeleNormValues.lean`, which the AF27
skeleton did not import) and the "untyped binder" failure was `open scoped NNReal` missing, without which
`ℝ≥0` in the `let α` block is an inequality rather than the type. With the pin's own imports and scoped
opens both statements elaborate **verbatim**, and the pair is now landed: two modules, two orders, run in
parallel. `Adelic/WeylIntegrable/FiniteSlice.lean` (**265 lines / 15 declarations, 15 ok / 0 / 0**) is the
most striking composition measurement in the column: the pin file is 1,349 lines and 175 indexed
declaration rows, and **172 of them were already byte-identical** in the port (verified by recomputing
statement hashes over `WeylIntegrable/{Coset,Transfer,BoxBounds,LatticeEstimates,Assembly}.lean`), so the
module adds five blocks and 170 lines of Lean. `Adelic/LocalIntertwiningFinprod.lean` (**1,315 lines / 87
declarations, 87 ok / 0 / 0, nothing private**) is the finite-adèle Euler product of the unramified
integral — a genuine transcription whose mathematics is the landed local identity
(`integral_unramifiedWeylIntegrand_adicCompletion`, 2,110) and whose `m_prod` premise only licenses the
`tprod` limit. Both dropped the pin's heartbeat overrides (B's pin file asks for
`maxHeartbeats 4000000`) and fit the 200,000 budget. The re-read: `needed` **765 / 321,659 →
763 / 319,019**, frontier 1,651 / 805,717 → 1,653 / 808,357, ready 62 / 16,628 → **60 / 13,988**, leaves
204 / 52,711, `AutomorphicForm` demand 275 / 121,503 → **273 / 118,863** — and the forecast's two wrong
cells (it subtracted the 1,072 *net* where the demand counts the 2,640 *silo*) are recorded as the second
instance of AF24's arithmetic rule.


The thirty-fourth **is landed** (2026-11-08): [automorphicForm/SET-AF34.md](automorphicForm/SET-AF34.md),
the **genuine smooth cusp realization** — its central character (modulus and continuity), the level-one
Hecke obstruction over an arbitrary number field, and the `‖det‖^t` twist. Four orders on four new
modules plus one `Def_` port (`AutomorphicForm/Adelic/FnTwist.lean`, 14 ok), 5 nodes / 1,939 silo. Two
measurements are the set's own. **First, a false ready row**: the general obstruction row read
`needed = 1` while its pin proof cites `NumberField.denseRange_algebraMap_add_adeleSingleAt`, which the
port did not hold — it held `RatAdele.denseRange_…`, the `K = ℚ` case at the *same last name*, so the
name tier counted the general node as ported (FR-0156; `--unport` is the instrument, and the 333-line
premise became the set's first order). **Second, the specialisation is derived**: the pair
`not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` (527) / `…_of_continuous` (513) is
parallel in the pin (neither cites the other), and `productionPinsGeneral ℚ` unfolds *definitionally* to
the general row's pins, so the `ℚ` headline is a three-line application and its 513-line `ℚ`-only
argument is not transcribed (verified twice by probe before dispatch). The re-read: `needed`
**763 / 319,019 → 759 / 317,413** and literal 775 / 322,484 → **771 / 320,878**, both exact; frontier
1,653 / 808,357 → 1,657 / 809,963 and `NumberField` demand unchanged 99 / 34,198, because the instrument
never counted the shadowed premise at all (§8.3); ready 60 / 13,988 → **59 / 13,881**, leaves
204 / 52,711 → **203 / 52,512** (the central-character row is a *leaf*), `AutomorphicForm` demand
273 / 118,863 → **269 / 117,257**. Rows readied: `LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet`
(**1,187**) and `SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` (113, leverage 1/16) — so
the column's ready head is now the 1,043 induced-section/height row and that 1,187-line Satake bound.


The thirty-fifth **is landed** (2026-11-08): [automorphicForm/SET-AF35.md](automorphicForm/SET-AF35.md),
the **Satake bound at level one** — the chain SET-AF34 readied. Three rows / 1,780 silo in 1,798 written
lines (the first set of the column whose written lines exceed its silo: the 1,187-line pin file is a genuine
transcription, port 1,223 lines / 68 declarations / 5 ok). `Cusp/SatakeParameters.lean` produces the unitary
input `‖b v‖ = 1` from a covariant self-pairing; `Cusp/SatakeBound.lean` forces both Satake roots strictly
inside `√N` and gives `a² ≠ b·(N+2+N⁻¹)`; `Cusp/SatakeConsequence.lean` (126 lines) is the pin's assembly,
producing that input from the Petersson pairing and reading the bound off the `‖det‖^t` twist, with the
`t = (1-s)/2` `rpow` cancellation exactly as the pin's. No definition layer, no promotion, no migration.

The thirty-sixth **is landed** (2026-11-08): [automorphicForm/SET-AF36.md](automorphicForm/SET-AF36.md),
the **Whittaker-ODE engine** — the first cut the column made on the *leaves* shelf. Three premise-free
`LanglandsTunnell` leaves / 1,955 silo in **1,358 written lines**: the general linear-dependence lemma at
moderate growth (711 pin lines, transcribed **verbatim** — a `diff` against pin `:21–711` has exactly two
hunks), its `(ν²).im = 0` companion *derived* (18 lines against a 643-line pin file), and the forced
near-zero growth bound (601, five `convert` drifts only, no `rpow` rename). No `Definitions/` module at all:
the pin files import mathlib only. **It readied two rows** (361 + 329 = 690 silo) — the best
unblocking-per-line figure the column has recorded since SET 3's leaf tail.

The thirty-seventh **is landed** (2026-11-08): [automorphicForm/SET-AF37.md](automorphicForm/SET-AF37.md),
the **Weyl translate of an induced section, evaluated** — the value side of AF33's subject. Three rows /
1,620 silo in 1,307 written lines with **464 declaration lines imported**: the bottom-row indicator row
(1,043 pin lines / 82 declarations) writes only 46 of them, because 31 are hash-identical to the imported
`InducedSectionFlat` prelude, 1 is its private `coe_mul`, and 4 are the homed `PlaceModulus.*`. The two
evaluations (archimedean 360, finite-place 217) sit in one module above `IwasawaWeylUnipotent`. One `own:`
row in `spec/decl_markers.tsv` (the pin's task-label-qualified `P6B.JE2aFlat.flatOne`).

The thirty-eighth **is landed** (2026-11-08): [automorphicForm/SET-AF38.md](automorphicForm/SET-AF38.md),
the **Γ₁ Hecke operators `U_ℓ` and `Diag_d`** — four rows / 1,158 silo in 1,084 written lines, including the
shelf's highest-leverage row (`exists_degeneracy_gamma1_hasNebentypus`, 9/12 consumers). The surface gate
did the set's real work: both modules landed at `2 ok` with their pin-public helpers `private`, and stripping
`private` moved them to **34 ok** and **33 ok + 3 own** with no proof changed (FR-0160). It **readied two
rows** (69 + 218), the second being the level-raising linear-independence statement. One definition-layer
gap surfaced: `Def_FreyPackage_ModMCarrier_Rescale` is imported by the pin's file but is not in
`--with-defs`'s statement closure, so two of its declarations are carried and marked `own:` (FR-0161).


The thirty-ninth **is landed** (2026-11-08): [automorphicForm/SET-AF39.md](automorphicForm/SET-AF39.md),
the **right-convolution engine at a level coset** — three rows / 825 silo in 791 written lines, with 6 of
39A's 19 pin declarations *reused* from `LevelCompactness`/`TestFnInvariance` rather than re-declared (a
second public `AutomorphicForm.sandwich` would break any module importing both). The set's honest note is
that the port already held row C **generalized** (`SpectrumLift.cosetSum_rightConv_eq`, arbitrary `U ≤ K_f`):
46 of row C's 101 proof lines re-prove that argument, and the recipe's FR-0041 check — grep for a
*generalized* copy, not only for a statement twin — would have priced it before dispatch. Its three helper
copies are 49 lines, of which 22 are packaging (element extensionality, the arch/fin commutation) and 26 the
double-coset transversal argument.

The fortieth **is landed** (2026-11-08): [automorphicForm/SET-AF40.md](automorphicForm/SET-AF40.md),
the **idèle product-measure layer** — the definition-layer set SET-AF39 §1 deferred. It is three modules
plus two declarations, because the pin's `Def_NumberField_IdeleProductMeasure` imports a chain
(`Def_IsDedekindDomain_FiniteUnitIdelesOutside` → `Def_UnramifiedWhittaker_ZetaIntegrand`) that was also
unported: **7 + 2 declarations of new modules, 2 added to `FiniteIdeles`, and 64 in
`NumberField/IdeleProductMeasure.lean`** (694 lines, 42 ok + 1 own, 43/43 axioms clean), of which the
manager wrote the twelve definitions and order AF40A the 53 bodies in 525 lines. The row it unblocks — the
**Borel Haar disintegration** `∫⁻ b, F b ∂μB = c · ∫⁻x∫⁻u∫⁻t, F (n(x)·z(u)·diag(t))·‖t‖⁻¹` (429 silo) — is
scaffolded checker-green and is order AF40B; before this layer it could not even be *stated*, which is the
concrete answer to "run `--with-defs` once per set" (FR-0161: that gate closes over statement vocabulary,
not over the pin's `Definitions/` import chain).

The forty-first **is landed** (2026-11-12): [automorphicForm/SET-AF41.md](automorphicForm/SET-AF41.md),
the **near-zero growth bound at the cusp** — the unforced Whittaker pair
(`norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode` 443 and its `|Re ν| < 1/2` sibling 427,
the second *derived* in 11 lines because the first's `ε`-form already gives it) together with the three
elementary ODE bounds the torus-system estimates rest on (Bessel 420, first-order system 240, first-order
Euler 128). **5 premise-free leaves / 1,658 silo in 828 written lines**, 988 module lines over two new
modules; no definition gate (the five pin files import mathlib only), no legacy module, no migration.
Its manager's layer is the column's cleanest promotion measurement yet: `port_advise` reported 24 names
byte-identical to `private` declarations of AF36's forced development, and promoting those 33 declarations
(the 24 plus the nine `def`s their statements mention) took `WhittakerODEGrowth.lean` from **1 ok to
34 ok / 0 mismatch / 0 missing** with two widened wires and a silent 19 s build — after which order 41A's
six transcribed bodies compiled **first try** with zero re-statements, so the 327-line prelude the pin
copies into both files was *imported*. The set's second saving is its own dedup: the pin states its
first-order argument twice (`OdeCAux.main` ≡ `Gap41.odeC`, identical statements), so the port proves it
once and keeps the pin's second name as one application — 106 → 8 removable lines, checked surface
unchanged at 10 `ok` (FR-0165). Three v4.34 frictions came out of it and are recorded: the
`convert … <;> try … rfl` idiom now warns (`unnecessarySeqFocus`/`unusedTactic`, FR-0163), a pin
hypothesis the pin never uses cannot be renamed or suppressed (FR-0164), and `dedup.py --within` is a
flag, not a pattern (FR-0162). The re-read is **exact on all seven cells**: `needed`
**742 / 309,646 → 737 / 307,988**, literal 758 / 315,065 → 753 / 313,407, frontier 1,669 / 814,882 →
1,674 / 816,540, ready 50 / 9,171 → **53 / 10,555**, leaves 200 / 50,557 → **195 / 48,899**,
`AutomorphicForm` demand unchanged 260 / 113,790, `LanglandsTunnell` 33 / 13,790 → **28 / 12,132** — and
the return is exactly the three rows the brief named before dispatch (508 + 499 + 377): the
**torus-system block** is AF42, with `casimir_pos_or_discrete_or_zero_of_weightSet` (139) as its
`CuspidalConstituent` edge.

The forty-second **is landed** (2026-11-12): [automorphicForm/SET-AF42.md](automorphicForm/SET-AF42.md),
the **Casimir trichotomy and the growth of the torus-system solutions** — the four rows the previous set's
return column named: the trichotomy (`λ > 0`, `λ = k(k−2)/4` discrete, `λ = 0`, from a non-empty `±2`-closed
weight set) and the three growth regimes of an `n`-step `SU(2)`-string solving the `GL₂(ℂ)` Whittaker
system. **4 rows / 1,523 silo in 1,179 written proof lines** over a 421-line scaffold, landing as
`LanglandsTunnell/TorusSystemGrowth.lean` (**1,561 lines, 54 ok / 0 / 0**, all four headlines axiom-clean,
4.1 s–21 s silent builds). Its price is the column's extreme: **1.03 module lines per silo line**, because
it is a pure transcription with nothing already in the port — and its *composition* is the other
measurement: the four pin files cite exactly the five `S_` files SET-AF41 landed, and the proof of
`AlphaAux.main` is the pin's own route through them (`sysN` ← the diagonal-system bound,
`norm_block_le` → `norm_Bn_le` → `hB`, `f_eq` reassembling the string) with the exponent `1 − ε` intact.
Return: **zero**, as pre-dispatch measurement said; the three torus rows' consumers each owe two or more
premises, so the set is a chain head and the brief says so. The re-read was exact on all six cells:
`needed` **737 / 307,988 → 733 / 306,465**, ready 53 / 10,555 → 50 / 9,171, leaves 195 → 194 / 48,760,
`LanglandsTunnell` demand 28 / 12,132 → 24 / 10,609.

The forty-third **is landed** (2026-11-12): [automorphicForm/SET-AF43.md](automorphicForm/SET-AF43.md),
the **`Γ₁` level-lowering separation, the cusp-space structure and the diamond divisor sums** — the first
cut in the `ModularForms` (`Γ₁`) layer since SET-AF38, and the shelf's best return. **7 rows / 1,203 silo
in 1,057 written proof lines** over three scaffolds of 261 lines: `ModularForms/NebentypusSeparation.lean`
(**815 lines, 55 ok**, the split of a `Γ₁(N)`-invariant divisor sum into the levels `Γ₁(N/p)` and the
multiplicity-one independence of degeneracy lifts), `ModularForms/Gamma1CuspStructure.lean` (**250, 12 ok**,
commuting `U_ℓ`, the primitive-form vanishing criterion, an integral basis, finite dimension) and
`ModularForms/CohCarrier/DiamondDivisorSum.lean` (**260, 1 ok**, the weight-four Eisenstein witness for the
diamond action). Return **as measured**: `ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem`
(485) and `CuspForm.IsEigenformWith.fg_adjoin_qCoeff` (291) readied, 776 silo of new work for 415 silo of
the set. Three method findings came out of the wave and are recorded: the **scaffolder's blind spot**
(FR-0166 — a scaffold carries the *statement's* import closure, not the proof's: four project imports were
added by ruling after the checker had already certified the scaffolds at 55 ok); the **heavy-closure
re-proof trade** (FR-0167 — `CuspForm.StableU` re-proved as a 62-line `have` rather than importing
`ModularCurve/Period/HeckeStability`'s `EichlerShimura`-bearing closure, with the cost recorded); the
**heartbeat-headroom instrument** (FR-0168 — probe by *lowering* the gate: the worst proof of the pin's
3,200,000-heartbeat file sits in [5k, 10k], a 20×–40× margin); and one genuine v4.34 elaborator divergence
that no budget fixes (FR-0169, the pin's `Summable.mul_left` one-liner). The wave's re-read: `needed`
**737 / 307,988 → 726 / 305,262** (−11 nodes / −2,726 lines, both sets' silo to the line), ready
53 / 10,555 → **45 / 8,744**, leaves 195 → **194 / 48,760** — exact except one bookkeeping cell (the
seventh row is `ModularForm`-namespaced and was subtracted from `CuspForm`, so `CuspForm` reads
34 / 11,498 against a forecast 33 / 11,261). Named next by measurement: the 868-line
`CuspForm.exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero`, one premise away from this
set's A1.

The forty-fourth **is landed** (2026-11-12): [automorphicForm/SET-AF44.md](automorphicForm/SET-AF44.md),
the **valuation approximation toolkit** — cut on the **leaves** block, as the recipe's §1 says to read it,
and the best return-per-silo cut the column has measured. Four premise-free `ValuationSubring` leaves
(2,004 silo: the normalization of a sum by `A`-coefficient conditions, partial fractions at infinity
`p(f)/t(f) = p₁(f)/t₁(f) + q(f⁻¹)/s(f⁻¹)`, the constancy criterion, and strong approximation for an
antichain of valuation subrings) readying **five rows / 1,848 silo** — 0.92 of the set's own cost, against
637 for the `CuspidalConstituent` leaf block, 199 for the Dedekind Euler product, 106 for the idèle/Haar
quotient and **0** for `NumberField.AdelicBox`. Landed in two orders over three mathlib-supplement modules
in the port's `FieldTheory/`: `ValuationSubringPolynomial.lean` (**1,058 lines, 69 ok**),
`…PartialFraction.lean` (**709, 62 ok**) and `…Approximation.lean` (**339, 17 ok**) — **148 public
statements verified verbatim, 134 proofs**, every module silent, all four headlines axiom-clean, 0 dead
declarations. The pin files all carry `import Mathlib`, which the port does not: the three modules are
built from thirteen specific mathlib modules, and the one that had to be discovered by search is
`RingTheory/Valuation/LocalSubring` (the sole v4.34 home of `iInf_valuationSubring_superset`). Two findings
came out and are recorded: the **namespace-shadowing trap** (FR-0170 — inside `namespace ValuationSubring`,
mathlib's own `ValuationSubring.add_mem`/`neg_mem`/`mul_mem` shadow `Subring`'s, so ten pin-transcribed
sites had to name the points; a general hazard for any port that nests a pin label namespace under a
mathlib namespace) and the **consumer-instance lesson** (FR-0171 — both orders' suggested instances, `t = X`
and `t = 1 + X`, were *impossible mathematics*, not name mismatches, and were replaced by the pin's own
`1 - C c * X`). The re-read is exact on all eight cells: `needed` **726 / 305,262 → 722 / 303,258**, ready
45 / 8,744 → **50 / 10,592**, leaves 194 / 48,760 → **190 / 46,756**, `ValuationSubring` demand
24 / 6,218 → **20 / 4,214**, and the five readied rows to the line (870 + 427 + 337 + 138 + 76). Named
next: the two rows the 427 unlocks (1,082 + 848), the rest of the `ValuationSubring` block
(20 rows / 4,214, including `isPrincipalIdealRing_of_finiteDimensional_adjoin` at **36 project
consumers**), and — outside any story — `M4aTorus.completedRayL_fe`, **12,126 silo**, the shelf's largest
node by a factor of three, which is a mechanical-transcription set on the AF7 pattern rather than a story.

The forty-fifth **is landed** (2026-11-12): [automorphicForm/SET-AF45.md](automorphicForm/SET-AF45.md),
the **regular prolongation's residue calculus and the valuation subring's denominators** — five of its six
rows are the rows SET-AF44 readied, taken with the one leaf of the same subject, so the set is the chain
AF44's return column pointed at. **6 rows / 1,337 silo in 1,034 written proof lines**, landing as an
**insertion** into the port's `AlgebraicCurve/RegularProlongationFinrank.lean` (1,568 → 2,015 lines; the
home is decided by subject, since that module already held five of the pin's `RegularProlongation` nodes)
and a new `FieldTheory/ValuationSubringFinrank.lean` (861 lines, 16 declarations, including the
`isPrincipalIdealRing_of_finiteDimensional_adjoin` row with **36 project consumers**). Both are green —
**62 ok** on the hub (unchanged) and **16 ok** on the new module — silent at the default 200,000-heartbeat
budget (the new module is silent even at 30,000), all six headlines axiom-clean, the hub's dependent
`Place/ConstantFieldExtension.lean` still building (the insertion's cascade is clean), and **0 dead**.
The return is **five rows / 2,146 silo**, including the 1,082 and 848 rows AF44 §7 named. Three findings:
the **qualified-`end` artefact** (FR-0172 — the pin closes its label namespaces with `end A.B.C`, which
cannot resolve inside the port's nested namespaces, and `check_port` cannot see it because it never
elaborates); **`linter.style.haveILetI` is on by default at v4.34** (FR-0173 — eleven `haveI`/`letI` walls
rewritten to `have`/`let`, which register the instance anyway); and the **`ValuationSubring` shadowing is
wider than AF44 recorded** (FR-0174, superseding FR-0170 — besides `add_mem`/`neg_mem`/`mul_mem`, the bare
`eq_top_iff` silently means `ValuationSubring.eq_top_iff`, and `IsLocalHom`'s field is `map_nonunit`). The manager's own edits: one approved import on the hub (`ValuationSubringApproximation`,
the module AF44 had landed two hours earlier — the fifth FR-0166 instance in three waves, and the first
where the column feeds itself), and one **dedup merge** of five intra-module copies the pin's two files
produce (`constHom`, `coe_constHom`, `residue_constHom`, `aeval_eq_linearCombination`,
`linearIndependent_pow_iff_transcendental`): one proof each, the second pin name kept as a one-line
application, 59 → 42 removable lines with the checker unmoved. The re-read is exact on six of seven cells
(`needed` **722 / 303,258 → 716 / 301,921**, ready 50 / 10,592 → **52 / 11,898**, leaves 190 / 46,756 →
**187 / 46,259**, `ValuationSubring` 20 / 4,214 → **16 / 3,380**, `AlgebraicCurve` 48 / 19,391 →
**46 / 18,888**); the literal cell is four lines off because the brief's subtraction said 307,344 where
308,677 − 1,337 = 307,340 — arithmetic, not the model. Named next: the four rows that are now one premise
away (largest `ValuationSubring.exists_valuation_mul_eq_one_of_finrank_le_card`, 1,062) and
`RegularProlongation.exists_prolongation_of_card_roots_eq` (613), with `M4aTorus.completedRayL_fe` priced
as the queued big effort (four unported `Def_` modules, 1,139 pin lines, then 742 declarations).

The forty-sixth **is landed** (2026-11-12): [automorphicForm/SET-AF46.md](automorphicForm/SET-AF46.md),
the **residue map's Gauss basis and its rank** — 4 rows / 2,119 silo, and the column's second *mechanical*
set after AF7. The measurements decide the strategy: a statement-by-statement scaffold is the wrong
instrument when the pin's declarations carry `LinearMap`/`RingHom` structure literals and `letI`-scoped
modules, because cutting a def body **changes the surrounding implicit binder lists** (a section variable
used only by a body drops out of the signature) — the manager hit exactly that and switched routes. The
mechanical copy (the pin's text, the tooling translated) landed at **zero `sorry` and zero statement
changes**: `AlgebraicCurve/RegularProlongationResidueSpan.lean` (966 lines, 26 `ok`, 32 warnings cleared)
and `…GaussBasis.lean` (1,244 lines, 50 `ok`, 14 elaboration sites and 49 warnings cleared), both silent,
both axiom-clean, 76 `ok` between them. The set's findings are instrument-level: **`check_port` compares
statement text, so it cannot see a name-resolution change** — the pin's bare `residue` means
`IsLocalRing.residue`, the port's `namespace RegularProlongation` resolves it to the structure field, and
the declaration read `ok` while its meaning had drifted; the answer is a `local notation` giving the pin's
meaning *with* the pin's text (FR-0176). Second, v4.34 turned `ResidueField` from an `abbrev` into a `def`,
so mathlib's `Module (R ⧸ I) (M ⧸ I • ⊤)` no longer fires through it — the port opens the file's own
scoped instances rather than the pin's `attribute [-instance]` shim (FR-0177). Third, the wave caught a
**port duplicate at the import boundary**: `coeff_mem_of_aeval_mem_integers` was declared in two modules,
so importing both failed; the manager kept the namespace owner's copy and deleted the fully-qualified one,
10 → 9 `ok` (FR-0175). And one ruling now stands in the record: **`omit` is not a silencer** — it shapes a
signature, so the pin's `omit [Fintype ι] in` stays, and only `set_option linter.… false` is forbidden. The
re-read: `needed` **716 / 301,921 → 712 / 299,802**, literal 732 / 307,340 → **728 / 305,221**, ready
52 / 11,898 → **50 / 10,210**, `AlgebraicCurve` 46 / 18,888 → **42 / 16,769**, two rows readied (261 +
170); the frontier cell is 238 lines off because the brief's addition slipped (822,607 + 2,119 = 824,726,
not 824,488) — the model, a per-set subtraction, was exact in every other cell. Named next: the four rows
AF45 moved to one premise (`ValuationSubring.exists_valuation_mul_eq_one_of_finrank_le_card` 1,062 and the
`ord_residue` / `existsUnique_place` / `gaussBasis` successors), then `M4aTorus.completedRayL_fe`
(12,126 silo, four unported `Def_` modules), and **the residue calculus chain AF44→AF45→AF46 is now
complete** — the regular prolongation's bound, its Gauss basis, its rank equality and the `L²` comparison
are all in the port.

The forty-seventh **is landed** (2026-11-12): [automorphicForm/SET-AF47.md](automorphicForm/SET-AF47.md),
the **value group of a complete splitting** and the **residue field of a valuation subring** — the chain
AF46 §4 named as next, taken whole with the two small nodes that gate the residue-field side of the same
cone. **5 rows / 2,153 silo / 1,475 net**, a *scaffolded* set (the AF44 shape, not the AF46 mechanical
one): four new `FieldTheory/ValuationSubring*.lean` modules, **42 declarations and 41 checker-green
statements written before a single proof**, 630 → 1,652 lines, the five data definitions (`composite`,
`locAt`, `coarsen`, `bar`, `resHom`) transcribed, the pin's ~500-line duplicated prelude imported from the
two modules that already held it (**18 declarations, ≈331 lines**, the largest dedup the column has
measured in absolute terms), and the pin's task-label namespaces rectified. Three orders landed with
**zero `sorry`**: 41 ok / 0 mismatch / 0 missing (unchanged from the scaffold, so no statement moved), all
eight probed declarations (the five headlines and the three engines) axiom-clean, all silent at the project
cap, `dedup`/`move_dead` empty, three consumer zones at 0 errors. The re-read: `needed` **712 / 299,802 → 707 / 297,649**, leaves 187 → 185, `ValuationSubring`
demand 16 / 3,380 → **11 / 1,227**, and **three** rows readied (1,083 + 1,090 + 613) rather than the two
the brief forecast — D2's 200 in-graph consumers produce one more. The set's instrument finding: **the
scaffold moves the shelf, the proof does not** (the read taken with the scaffolds and the read taken after
landing are identical in all eight cells, FR-0114 at set scale). Findings: a scaffold's imports must be
closed over the *port* modules, not the pin's `Theorems/` lines (FR-0181); a `local instance` does not
travel through `import`, so a `ResidueField`-hypothesis consumer must re-install `residueAlgebra`
(FR-0182, the FR-0177 trap from the consumer side); and a consumer instantiation must be checked against
the *lattice* too — `ValuationSubring` has no `OrderBot` (FR-0183, FR-0171's fifth instance). Named next:
the three readied rows (`existsUnique_place_forall_residue_sub_mem_nonunits` 1,083,
`ord_residue_le_sum_ord_of_isIntegral_adjoin` 1,090, `exists_prolongation_of_card_roots_eq` 613 — the
prolongation of regular local data), then `M4aTorus.completedRayL_fe` (12,126 silo, four unported `Def_`
modules) and the `EisensteinGeneral.Piece` factorization story (890, six `Def_` wrappers).


The forty-eighth **is landed** (2026-11-12): [automorphicForm/SET-AF48.md](automorphicForm/SET-AF48.md),
the **reduced place on a chart** and **Deuring's multiplicity inequality** — the two rows AF47's landing
readied and named first. **2 rows / 2,173 silo / ≈2,105 net in 81 declaration groups**, two new modules
(`AlgebraicCurve/RegularProlongationReducedPlace.lean` 390 → **1,108** lines / 43 declarations /
**44 ok** / 43 → 0 `sorry`, `AlgebraicCurve/DeuringMultiplicity.lean` 351 → **1,124** / 36 / **35 ok** /
35 → 0), the pin's namespace/section structure verbatim, its `p2m_open` translated to `open`, the 84-line
`attribute [-]` shim and the pin's `set_option maxHeartbeats` dropped, and the pin's machine labels
rectified (`ExUniqPlace` → `ReducedPlace`, `ORLS` → `DeuringMultiplicity`). Two concurrent orders, both
silent, axiom-clean, `dedup`/`move_dead` empty, two consumer zones at 0 errors. **The two sets together
(AF48+AF49) moved `needed` 707 / 297,649 → 703 / 294,693** (the four rows' 2,956 lines exactly), the
`AlgebraicCurve` demand 42 / 16,769 → **38 / 13,813**, and readied **two rows / 1,303 silo**
(`sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin` 758, lev 1/1; `residue_integralClosure_surjective_of_genusFF_eq`
545, lev 1/10 with **17 premises** — the next order's risk node). One instrument finding: the frontier needed
an eleventh `--unport`, **MD-006** (`ValuationSubring.isIntegral_of_forall_mem`, a 176-line pin node the port
does not have, read as ported because two new modules declare a same-last-name lemma) — the FR-0047 shadow
in the *inflating* direction; corrected, the frontier is 1,703 / 828,332 and every cell closes.

The forty-ninth **is landed** (2026-11-12): [automorphicForm/SET-AF49.md](automorphicForm/SET-AF49.md),
**Kummer splitting** and the **Gauss degree bound** — **2 rows / 783 silo / ≈740 net in 57 groups**,
`AlgebraicCurve/RegularProlongationKummer.lean` (397 → **630** lines, 55 ok, 47 → 0 `sorry`, the pin's nine
data definitions transcribed) and `AlgebraicCurve/RegularProlongationGaussDegree.lean` (72 → **212**, 1 ok,
1 → 0 — the whole 170-line pin file, whose `set_option maxHeartbeats 4000000` the port deliberately does not
carry; measured, that proof costs **27,000–28,000 heartbeats**, ~14 % of the gate, so the pin's override was
never needed). One order, both modules silent, axiom-clean, consumer at 0 errors. **Not** the
`exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_*` pair those rows look like they ready: that pair is
gated on A1 *and* on three further unported premises (193 + 216 + 262 silo), so it enters a later set as its
own story. Two instrument findings recorded on the way: a scaffold must price **before** it is written
(FR-0184 — `port_plan` reads the scaffold as "already in the port", 2,100 lines of AF48 collapsed to
"net 13"), and the pin's per-file `maxHeartbeats` is a risk marker to be probed, not carried.

The fiftieth **is landed** (2026-11-12): [automorphicForm/SET-AF50.md](automorphicForm/SET-AF50.md), the
**ord equality of a chart** and the **residue map's surjectivity at equal genus** — the two rows AF48's
landing readied. **2 rows / 1,303 silo / ≈1,100 net in 80 declaration groups**, two new modules
(`AlgebraicCurve/RegularProlongationSumOrdResidue.lean` 355 → **798** lines / 53 declarations /
**54 ok** / 46 → 0 `sorry`, `AlgebraicCurve/RegularProlongationResidueIntegralClosure.lean` 252 → **573** /
24 / **26 ok** / 23 → 0), the pin's structure verbatim and its labels rectified (`SOSR` →
`SumOrdResidue`, `CbPrime` → `ResidueIntegralClosure`). Two concurrent orders; B1 is the set's
**seventeen-premise** row and got its own order and wall time — and it closed positive (all seventeen
premises strong enough for the pin's proof verbatim; the only gap was the scaffold's import cone). **AF50+AF51
together moved `needed` 703 / 294,693 → 699 / 292,705** (the four rows' 1,988 lines exactly), `AC` demand
38 / 13,813 → **36 / 12,510**, `NumberField` demand 99 / 34,198 → **97 / 33,513**, and readied **one row /
398**. Findings: the manager's import cone omitted two port modules that block a whole chain (FR-0181,
third and worst instance — the worker proved the lemmas unreachable by computing the closure of all 14
frozen imports before asking); a one-line pin proof needing ≥2,000,000 heartbeats is a `Subtype.val`-under-
`ord` defeq trap, rewritten rather than budgeted (FR-0187); and one headline landed in the pin's
file-level `P2MW` namespace with the checker reading `1 ok` (FR-0186 — the checker matches content, so a
headline's *name* must be asserted too).

The fifty-first **is landed** (2026-11-12): [automorphicForm/SET-AF51.md](automorphicForm/SET-AF51.md),
the **Euler product of the Dedekind zeta** and the **regularized zeta** — the column's first
`NumberField.CompletedDedekindZeta` set since that package landed. **2 rows / 685 silo / ≈630 net in 44
groups**: `…/CompletedDedekindZeta/EulerProduct.lean` (252 lines, 43 declarations, **43 ok**, 38 `sorry`s,
the nine data definitions incl. the scoped `finite_fiber` instance) and `…/CompletedDedekindZeta/RegularizedZeta.lean`
(54 lines, 1 declaration, **1 ok**, 1 `sorry` — the whole 105 pin lines, and **18 in-graph consumers**, the
column's cheapest high-leverage row in a long time). The pin's machine label `Ws41` is rectified to
`EulerProduct`, `N1bProof` to `ArchimedeanNormalization`; one v4.34 deprecation applied at generation
(`Ideal.finite_setOf_absNorm_eq` → `…setOfPred_absNorm_eq`, now a drift-table row). The two rows are priced
at ≈1,100 and ≈630 net, and both briefs state the FR-0184 caveat explicitly: `port_plan` on the scaffolded
tree reads "net 19" and "net 8" because the scaffolds themselves are in the port.

## 6. Verification and wiring

- **Checker.** Every port module carries its own `spec-pin:` header; the legacy `PORT_FILES` /
  `SOURCES` lists are the handover path, not the destination (`spec-pin:` lines in, `PORT_FILES`
  entry out). The 2026-11-02 sweep did the whole class at once: **32** `Def_` transcriptions that
  had been wired by per-declaration `-- pin:` markers (684 of them) now carry `spec-pin:` headers,
  the six that were still listed had their rows retired, and the checker reads **686 ok / 0
  mismatch / 0 missing / 6 own** over them, the six `own:` rows being statements the pin writes
  through since-deprecated spellings (`Ideal.inertiaDeg'`, `AlgHom.restrictDomain`) or that are
  port-own. See [automorphicForm/SET-AF3.md](automorphicForm/SET-AF3.md) §4.5 and FR-0096. The `identical` count is the progress metric;
  a new set's delta must equal its public surface, and pin-private matches verify through the
  dotted fallback and show as `promoted`.
- **Consumer.** `spec/AutomorphicFormConsumer.lean` carries a real executed zone per level — no
  `#check`: the adele/`GL₂` topology and Haar, the level lattice and subgroups, the smooth-vector
  submodule, the carrier pins and right convolution, the automorphic and `Kf`-smooth predicates,
  the windowed-Siegel norms and row isometries, the archimedean inclusion and types, the shared
  prelude's `testFn`, and the three headlines. Deleting any one module it imports must break it.
- **Axioms.** `#print axioms` on every headline returns `[propext, Classical.choice, Quot.sound]`.
- **Faithfulness.** A `def`/`abbrev` taking type arguments keeps the pin's `variable … in` form;
  header prose stays in `/- … -/` blocks (a `--` line comment mis-aligns the checker's namespace
  tracker).

## 7. Budget and risks

The definition layer is **2,544 pin lines / 314 declarations**, written at the port's 1.25–1.45
ratio → ≈2.9–3.4k written lines. The theorem layer is small by comparison: the shared prelude is
one ≈400-line home that replaces ≈705 lines of duplicated block; the two H1-served headlines are
their `solution`s plus, for principalLevel, ≈150 lines of level-specific layer; and the arch route
adds the `ArchProfile`-parameterized family and ~57 declarations of arch-character analysis,
together with the 326-line right-invariance development (`M1`) it consumes.

| # | risk | mitigation |
|---|---|---|
| 1 | mathlib drift `v4.33.1` → `v4.34.0` across `AdeleRing`/`InfiniteAdeleRing`/`RestrictedProduct`/`Matrix.GeneralLinearGroup`/measure theory | per-module `lake env lean`; the adaptations so far are recorded in §8 and are all import-level or `local instance`-level, none a statement change |
| 2 | instance diamonds around `glBorel`/`adeleBorel` | transcribe the pin's local `letI`/`haveI`; build `Local` → `Adele` → `GeneralLinear` in order |
| 3 | same last name, different statement across the headline family | the checker's dotted/pin-private fallback; order `SOURCES` so the interface copy wins; `OWN_PROOFS` only as a last resort |
| 4 | the arch route's `ArchProfile`-parameterized prelude re-deriving the home's level-independent part | import the home; only the `ArchProfile` structure, the generalized `Φ₂`/`fa`/`testFn` family and the arch-character extras were new (landed as `A2`) |
| 5 | `scoped instance`/`instance (priority := …)` declarations are invisible to the checker | keep the pin's exact form; record any port-own instance explicitly |

## 8. Recorded negatives and drift adaptations

**Mathlib-first audit.** `ContinuousSMulDiscrete`, `IsSmoothVector`/`smoothVectors`,
`adelicGLHaar`/`adelicAddHaar`/`glBorel` and `IsLevelOneMatrix`/`finiteLevelOne` are absent from
mathlib `v4.34.0`, so each is a genuine port. The base types `AdeleRing`, `InfiniteAdeleRing`,
`FiniteAdeleRing` and `Matrix.GeneralLinearGroup` are mathlib's and are adopted as the interface
from the first declaration.

**Drift adapted in place (statements unchanged).** `Ideal.finiteQuotientOfFreeOfNeBot` lives in
`Mathlib.LinearAlgebra.FreeModule.IdealQuotient`; the `Units` topology instances need
`Mathlib.Topology.Algebra.Group.Units`; `ProperSpace (v.adicCompletion K)` now needs
`[Ring.HasFiniteQuotients R] [Infinite R]`, both *derivable* from the pin's
`[Module.Free ℤ R] [Module.Finite ℤ R]` (`Ring.HasFiniteQuotients.of_module_finite`,
`Module.Free.infinite`), so `Local.lean` supplies them as `local instance`s rather than
rescaling the metric; the `group` tactic needs `Mathlib.Tactic.Group`; `ContDiffBump`'s function
interface now needs `HasContDiffBump (E F)`, supplied by
`Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension`; `Set.mem_setOf_eq`, `if_pos`,
`if_neg`, `zero_le'`, `dif_pos`, `dif_neg` are deprecated aliases; the modular-character local
notation `Δ` collides with mathlib's scoped `Δ` for the Laplacian once the analysis imports are
in scope, so `AdelicHaar/MulRightInvariant` spells the character out; and
`Units.isClosedEmbedding_embedProduct.isCompact_preimage` is now spelled
`Topology.IsClosedEmbedding.isCompact_preimage Units.isClosedEmbedding_embedProduct`. Files that
keep a pin `letI`/`haveI` wall or literal (unused) section variables carried a one-line
`set_option linter.… false` with the reason — **no longer allowed**: the later sets write
`have hν₀ : 0 ≤ ν.re := hν`, one line naming the pin's hypothesis (SET-AF41's Bessel headline, FR-0164). Two further v4.34
adaptations came in with SET-AF41 and cost one line each: the pin's
`convert … <;> try with_reducible_and_instances rfl` idiom now trips
`linter.unnecessarySeqFocus`/`unusedTactic`, so it is written as `refine h.congr_deriv ?_` plus the
coefficient identity — watching the sign, the `congr_deriv` orientation being the reverse of the pin's
`convert` (FR-0163) — and `open Real Set Filter Topology` no longer suffices for `Tendsto`/`𝓝`, which
wants `open Real Set Filter` with `open scoped Topology`. The AF42/AF43 wave added four more, all
proof-text only: `push_neg` → `push Not`; the `CuspForm.coe_zero/coe_add/coe_sub/coe_smul` aliases →
`FunLike.coe_*`; `haveI : <class> :=` → `have` (`haveILetI`); and one genuine **elaborator**
divergence — the pin's `(summable_pow_mul_geometric_of_norm_lt_one 4 …).mul_left 2` `whnf`s forever
at v4.34 at *any* heartbeat budget (measured at 2,000,000), so the intermediate summable function is
named first (FR-0169). The wave also replaced the "it fits the default budget" assertion by a
measurement: probe with `-DmaxHeartbeats=40000/20000/10000/5000/1000` and record the first failure
(FR-0168) — AF43A's worst proof sits in [5k, 10k] under the 200,000 gate. One recorded negative: the pin's `P2M.Util`
is **tooling only** (127 lines of elab commands, no lemmas), so a ported proof never needs a counterpart
for it; its imports of `Mathlib.Algebra.Order.Chebyshev` &c. do need re-adding (the scaffold's union
dropped one, for `sq_sum_le_card_mul_sum_sq`).

## 9. Reproduce

```bash
cd tools/deps
# the target's definition closure
python3 explore.py AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant
# the frontier row this foundation serves
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0
# the family prelude and its duplicated copies
python3 port_advise.py --target 'P2M/Sol/S_AutomorphicForm_exists_isFactorizableTestFn_*' --no-siblings
# price an edit before triggering its cascade
python3 build_ladder.py --edit FLTForHuman/AutomorphicForm/Adelic/TestFnNearIdentity.lean
cd ../lean
timeout 300 python3 spec/old_check_stmts.py
flock .lake/flt_build.lock timeout 900 lake build
```
