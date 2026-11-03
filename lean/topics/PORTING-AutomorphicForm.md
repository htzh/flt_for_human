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
keep a pin `letI`/`haveI` wall or literal (unused) section variables carry a one-line
`set_option linter.… false` with the reason.

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
