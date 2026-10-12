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
time.

## 6. Verification and wiring

- **Checker.** Every port module is in `PORT_FILES` and every pin source in `SOURCES` (appended
  last, so a bare last-name match cannot flip). The `identical` count is the progress metric;
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
timeout 300 python3 spec/check_flt_statements.py
flock .lake/flt_build.lock timeout 900 lake build
```
