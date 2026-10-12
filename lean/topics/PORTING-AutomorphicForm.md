# The automorphic / adèlic foundation — a math-first blueprint

The Deligne–Serre column's §7 defers two automorphic gates behind a fixed interface.
This blueprint is the **definition foundation** those gates and the two `AutomorphicForm`
ready-shelf rows stand on. It is deliberately a foundation effort, not a theorem effort:
we are not in a hurry, so the goal is that the layer is organized once, by mathematics,
before anything imports it. Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib
`v4.34.0`.

The first consumer is
`AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant`
— shelf row 3 at 508 silo lines. `frontier.py --ready` prices it `needed 1 / 508`, but
that is the `S_` file only: `--ready` is a citation-name test and cannot see
`Definitions/`. The hand-walk in §1 shows the real def closure is **14 modules /
2,544 pin lines**, of which one is ported whole. Nothing can be *stated* before this
lands, so it is the first thing the column builds. The promotion audit of §4 then adds
the one piece that is cheapest now and expensive later: a public home for the prelude
the pin copies into every file of the `isFactorizableTestFn` family.

**Status (2026-10-11).** Wave R (§3) and the whole definition layer **D0–D7** (§5) have landed:
18 new role modules. Checker **7924 identical / 0 mismatched / 0 missing** (7641 → 7924: +1 the
`continuous_glMap` promotion, +26 D0, +21 D1, +27 D2, +102 D3, +17 D4, +24 D5, +41 D6, +24 D7);
`lake build FLTForHuman Reserve` green (9,413 jobs) with no warnings in the new modules and no
`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/heartbeat overrides; `#print axioms` on the
D-layer headlines returns `[propext, Classical.choice, Quot.sound]`; `spec/AutomorphicFormConsumer.lean`
green with one executed zone per level (D0–D7) plus the projections and the premise. **H1 and T1
(the theorem layer) remain.**

*Drift found since D1 (mathlib v4.33 → v4.34), all adapted in place.* D2: the `group` tactic
needs `Mathlib.Tactic.Group`, and the pin's engine lemma carries overlapping `[ContinuousMul G]`
/ `[NonarchimedeanGroup G]` (linter suppressed with a comment). D3: `Ideal.finiteQuotientOfFreeOfNeBot`
(the D1 import above) and `Set.mem_setOf_eq`/`if_pos`/`if_neg`/`zero_le'` are deprecated
(`Set.mem_ofPred_eq`/`ite_eq_left`/`ite_eq_right`/`zero_le`); `Units.isClosedEmbedding_embedProduct.isCompact_preimage`
must be spelled `Topology.IsClosedEmbedding.isCompact_preimage Units.isClosedEmbedding_embedProduct`
with `Mathlib.Topology.Algebra.Group.Units` imported; and the split means `IdealBall`/`Level` must
import `AdelicHaar.Adele` (not just `Local`) for `T2Space (FiniteAdeleRing R K)`.

*Drift found in D1.* `Ideal.finiteQuotientOfFreeOfNeBot`
moved to `Mathlib.LinearAlgebra.FreeModule.IdealQuotient`; the `Units` topology instances need
`Mathlib.Topology.Algebra.Group.Units`; and `ProperSpace (v.adicCompletion K)` no longer elaborates
at the pin's generality because mathlib's `instNormedFieldValuedAdicCompletion` now needs
`[Ring.HasFiniteQuotients R] [Infinite R]`. Both are *derivable* from the pin's
`[Module.Free ℤ R] [Module.Finite ℤ R]` (`Ring.HasFiniteQuotients.of_module_finite`,
`Module.Free.infinite`), so `Local.lean` supplies them as `local instance`s and keeps the pin's
statement and proof; no port-local rank-one rescaling is needed.

Companions: [PORTING-DeligneSerre.md](PORTING-DeligneSerre.md) §7 (why the gates wait),
[porting-playbook.md](../porting-playbook.md) §2.1/§2.3/§2.4/§3.1/§3.2/§3.7, and the
organization precedent [deligneSerre/TOPIC-definitions-and-homes.md](deligneSerre/TOPIC-definitions-and-homes.md).

## 1. The first stone — the target's definition closure

The `S_` file imports four pin `Def_*` modules; walking their `Definitions/` import DAG
closes over 14 modules. Status against the port today:

| pin module | decls | lines | port status |
|---|---:|---:|---|
| `Def_NumberField_AdelicHaar` | 25 | 205 | **sliver** — 4 `T2Space` instances only |
| `Def_NumberField_AdelicLevel` | 119 | 813 | **sliver** — the `Projections` section only |
| `Def_AutomorphicForm_FactorizableTestFn` | 10 | 66 | **whole** |
| `Def_AutomorphicForm_RightConvolution` | 5 | 37 | none |
| `Def_AutomorphicForm_SmoothAutomorphicFnAt` | 16 | 90 | none |
| `Def_AutomorphicForm_ArchType` | 24 | 189 | none |
| `Def_AutomorphicForm_RowIsometryInvariance` | 12 | 210 | none |
| `Def_AutomorphicForm_WindowedSiegelSet` | 29 | 307 | none |
| `Def_AutomorphicForm_CarrierPins` | 12 | 76 | none |
| `Def_AutomorphicForm_AdelicLsXi` | 11 | 55 | none |
| `Def_AutomorphicForm_ConstantTerm` | 11 | 63 | none |
| `Def_AutomorphicForm_AutomorphicFnAt` | 8 | 71 | none |
| `Def_RepTheory_SmoothVectors` | 27 | 321 | none |
| `Def_Deformations_ContinuousSMulDiscrete` | 5 | 41 | none |
| **total** | **314** | **2,544** | ≈208 lines present (one whole module + two slices) |

The statement alone names `AdelicGL2` (`AdelicLsXi:12`), `levelOne`
(`AdelicLevel:589`, and its `IsLevelOneMatrix`/`finiteLevelOne`/`idealBall`/`idealBound`
chain), `finiteAdelicGL2Subgroup` (`SmoothAutomorphicFnAt:15`) and `rightConv`
(`RightConvolution:9`), whose body needs `AdelicHaar.glBorel`/`adelicGLHaar`. Only
`IsFactorizableTestFn` and `glFin` exist. The proof adds `adelicArchGLIncl`
(`ArchType:122`) and the whole `WindowedSiegel` norm/isometry chain.

**The mathematics, layer by layer** (this is the reading order, and the set order of §5):

1. **Adèlic measure theory.** The completions `K_v` and their integral subrings
   (proper/compact), then `𝔸_K` (Hausdorff, Borel, additive Haar), then `GL₂(𝔸_K)`
   (Borel structure, Haar). This is what makes `rightConv` and every integral in the
   target meaningful.
2. **Adèlic level.** The level function `idealBound`, the integral finite adèles and the
   level-`N` ball, the archimedean/finite projections, the level matrices and subgroups
   `finiteLevelZero/One`, `levelZero/One`, and the Hecke generators
   (`localUnit`, `heckeGenAt`, `heckeGen`). This is the vocabulary of "level-`N`
   invariance" and of the finite subgroup `levelOne ⊓ finiteAdelicGL2Subgroup`.
3. **Representation theory.** Smooth vectors for a topological group action and the
   discrete-`SMul` class they rest on. Generic, mathlib-first, and the first real reuse
   in the layer.
4. **Automorphic vocabulary.** `AdelicGL2` and its points/central scalars; the idèle-class
   and unitary characters and the `LsXi` L²-space; the carrier-pins hypothesis bundle;
   unipotents, constant term and cuspidality; the automorphic and cusp automorphic
   predicates; then `Kf`-smoothness and the smooth automorphic predicates.
5. **Smoothing.** Right convolution, factorizable test functions, the
   `continuous_and_hasCompactSupport` premise, and the archimedean/windowed-Siegel norm
   and row-isometry estimates the non-vanishing proof consumes.

The layer is small but central: `explore.py` records these definition modules in the
*statements* of 480 (`SmoothAutomorphicFnAt`), 435 (`FactorizableTestFn`) and 356
(`RightConvolution`) theorems. It is the doorway to a **143-module / 25,727-line**
`Def_(AutomorphicForm|RepTheory|AdelicDock|Deformations)` layer, which is why the
directory cut of §2 has to be right before the other 129 modules arrive.

**Do not over-scope.** The sibling ready row
`AutomorphicForm.cosetSum_rightConv_of_isLevelSphericalOfType` imports a *different*
def closure (`CuspidalConstituent`, `ArchSpherical`, `AdelicDock_LocalEmbedding`), and
the two gates import `ProductionPinsGeneral`. This blueprint carries only the 14-module
closure above; the rest is a counted optional tail, and each future consumer gets the
same hand-walk before its order is cut.

## 2. The file plan (math clarity)

Two organizing rules drive the tree: **one directory per theory** (playbook §3.2) and
**one module per mathematical role, not one per pin file** (playbook §3.1). The pin's
two mega-`Def_` files and its mixed `AdelicLsXi` are therefore split; the two landed
stubs are absorbed rather than grown.

```
FLTForHuman/
  NumberTheory/
    AdelicHaar/
      Local.lean           -- K_v: integral subring, residue field, proper/compact
      Adele.lean           -- 𝔸_K: Hausdorff topology, Borel structure, additive Haar
      GeneralLinear.lean   -- GL₂(𝔸_K): Borel structure, Haar
    AdelicLevel/
      IdealBall.lean       -- idealBound, integral finite adèles, the level-N ball
      Projections.lean     -- 𝔸_K → K_∞ / 𝔸_K^fin, GL₂ components (grows to the pin section)
      Level.lean           -- IsLevelZero/OneMatrix, finiteLevelZero/One, levelZero/One
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
      FactorizableTestFn.lean  -- moved; pin module ported whole
      TestFnTop.lean           -- moved; the continuous/compact-support premise
      TestFnNearIdentity.lean  -- NEW, public: the shared family prelude (§4.2)
      ArchType.lean            -- archimedean inclusion and archimedean types
      WindowedSiegel/
        Set.lean               -- norms, heights, the windowed Siegel set
        RowIsometry.lean       -- row isometries and their invariance lemmas
    UpperHalfPlane/            -- the landed ℍ quartet, moved here
      HyperbolicMeasure.lean
      FundamentalDomainVolume.lean
      SiegelSetCover.lean
      Gamma0FundamentalSet.lean
```

| pin module | home(s) | why split |
|---|---|---|
| `Def_NumberField_AdelicHaar` | `AdelicHaar/{Local,Adele,GeneralLinear}.lean` | three subjects: local fields, the adele ring, the linear group |
| `Def_NumberField_AdelicLevel` | `AdelicLevel/{IdealBall,Projections,Level,HeckeGen}.lean` | four subjects: level ball, projections, level subgroups, Hecke generators |
| `Def_AutomorphicForm_AdelicLsXi` | `Adelic/{Basic,LsXi}.lean` | the base type `AdelicGL2` is used by everything; keeps the hub stable |
| `Def_AutomorphicForm_ConstantTerm` | `Adelic/ConstantTerm.lean` | one subject; promote to `AutomorphicForm/Defs/` only if the ℍ branch consumes it |
| the other nine | one file each under `Adelic/` | already single-subject |

**Namespace policy.** Keep the pin namespaces (`NumberField.AdelicHaar`,
`NumberField.AdelicLevel`, `AutomorphicForm`, `FLT.SmoothVectors`); directories carry
the organization, namespaces carry the pin fidelity the checker relies on. The one
top-level pin class, `ContinuousSMulDiscrete`, stays top-level (no namespace in the pin).

**Hubs fixed now.** `Adelic/Basic.lean` (`AdelicGL2`), `AdelicHaar/GeneralLinear.lean`
(`glBorel`/`adelicGLHaar`), `AdelicLevel/Projections.lean` (`glArch`/`glFin`),
`AdelicLevel/Level.lean` (`levelOne`), `RepTheory/SmoothVectors.lean` and
`Adelic/ConstantTerm.lean` (`IsCuspidalFn`) are the modules everything later imports.
They are written whole, once, with the public surface the pin fixes; no later wave edits
them.

## 3. Consolidation now (wave R)

Touching a hub is a wave, and the wave costs the same whether or not the cleanup rides
with it (playbook §4c). The reorganization is therefore a single wave, run **before** the
new definition content, while the fan-in is still 0–2 importers:

| action | file | importers to fix |
|---|---|---|
| move | `AutomorphicForm/FactorizableTestFn.lean` → `AutomorphicForm/Adelic/` | `TestFnTop` |
| move | `AutomorphicForm/TestFnTop.lean` → `AutomorphicForm/Adelic/` | `spec/AutomorphicFormConsumer.lean` |
| move | `AutomorphicForm/HyperbolicMeasure.lean` → `AutomorphicForm/UpperHalfPlane/` | `FundamentalDomainVolume`, `SiegelSetCover` |
| move | `AutomorphicForm/FundamentalDomainVolume.lean` → `UpperHalfPlane/` | `Gamma0FundamentalSet` |
| move | `AutomorphicForm/SiegelSetCover.lean` → `UpperHalfPlane/` | `Gamma0FundamentalSet` |
| move | `AutomorphicForm/Gamma0FundamentalSet.lean` → `UpperHalfPlane/` | `ModularCurve/Analytic/PeterssonPairing.lean` |
| absorb | `NumberTheory/AdelicHaar/Topology.lean` → `Adele.lean` + `GeneralLinear.lean` | `TestFnTop` (at the new path) |
| keep | `NumberTheory/AdelicLevel/Projections.lean` | grows to the whole pin `Projections` section in D3 |

The `Topology.lean` stub is not a role module: its four `T2Space` instances are pin
declarations of the `Adele`/`GeneralLinear` sections. Growing the stub would leave a
parallel home for the same pin file and a second import path for every consumer; folding
it now removes the fork. `Projections.lean`, by contrast, *is* a role, so it stays and
receives the four dropped projection declarations (`archEval`, `finAdeleEval`,
`archComponent`, `finComponent`) when the whole node lands.

Mechanical edits: the six import lines above, the four `PORT_FILES` entries at
`spec/check_flt_statements.py:3450–3453` and `3971–3974`, and
`spec/AutomorphicFormConsumer.lean:9`. The checker maps declarations by name, so the
moves change no comparison — only the path list. `lakefile.lean` globs with
`.submodules`, so new subdirectories need no build-file change.

Measured cascade (`build_ladder.py --edit`): `Gamma0FundamentalSet` → 1 module /
284 lines ≈5 s; `TestFnTop` → 0; `Topology` → 1 / 148 ≈2 s; `Projections` → 2 / 248
≈4 s; `FactorizableTestFn` → 1 / 148 ≈3 s; `PeterssonPairing`'s consumer is the only
one that re-elaborates real mathematics. The whole wave is seconds, which is the point
of doing it now. Gates: tier-1 builds green and no warnings; checker
`0 mismatched / 0 missing` with the `identical` count unchanged (moves add no
declarations); `git status` showing only the wave's files.

## 4. The private layer — promotions, done now

Two questions with different answers: which pin-`private` declarations carry mathematics
another theory will state, and which repeated preludes must have one home. Both are cheap
now and re-elaborate a cone later.

### 4.1 The definition layer

Only two `private` declarations occur in the 14 modules, and they split cleanly:

| declaration | pin home | verdict |
|---|---|---|
| `continuous_glMap` | `AdelicLevel:210` (private) | **promote.** The pin itself has a *public* twin at `Def_AutomorphicForm_BaseChangePlaces:317`, and this is the generic continuity of the induced `GL` map used by every projection and embedding in the 143-module layer. Home it public in `AdelicLevel/Projections.lean` at the pin's name; when `BaseChangePlaces` lands its copy becomes a reuse, and `SOURCES` is ordered so the public copy wins. |
| `unipotent_mul_unipotent` | `ConstantTerm:11` | **stays private** — a matrix computation whose public face is `unipotentGL2_add`. |

The landed slices have no other promotion to make: `Projections.continuous_glMap` is the
same case, and the ℍ quartet's `box`/`cbox`/`fdoWitness`/`one_le_quadratic_form` are
transcription-local measure scaffolding whose public headlines (`volume_univ_eq_top`,
`volume_band_le`, …) already carry the mathematics. The two `TestFnTop` privates
(`continuous_ringEquiv_mixedSpace`, `continuous_archEntries`) are §4.2.

### 4.2 The theorem-layer prelude — the big one

`port_advise.py` over the eight-file `S_AutomorphicForm_exists_isFactorizableTestFn_*`
family reports **43 shared declarations / ≈705 removable lines**, every one of them
public somewhere in the pin. The three `rightConv_ne_zero_of_*` files are the core:
levelOne ↔ principalLevel share **385 lines / 41 proofs**, and each of the three shares
320 / 299 lines with `hasArchCharacterAt`. The prelude is the near-identity
factorizable-test-function construction — `bump₂`/`bumpAt`, `testFn`/`testFnR`/`fa`/`ff`,
`Kf`, the homeomorphisms `mixedHomeo`/`pairHomeo`/`matHomeo`, the radius lemmas,
`continuous_ringEquiv_mixedSpace` — real mathematics, not glue.

Decision: **one public home**, `AutomorphicForm/Adelic/TestFnNearIdentity.lean`, written
before any of the family's theorem modules. It carries the port's own namespace (not the
pin's `Ws1.H2K.Scaffold`); the checker matches by last name against the pin's
`hasArchCharacterAt` `Scaffold` block, which is the public copy — so `SOURCES` lists that
file **ahead of** the two private siblings. Each family theorem module then imports the
home and drops its copy, and `TestFnTop`'s private
`continuous_ringEquiv_mixedSpace`/`continuous_archEntries` fold in as well. The saving is
measured, `(copies − 1) × block`; the helpers a theorem file alone needs stay `private`
in that file (the adapter rule).

This is the piece the user's "promote now" point is really about: the home is on the
critical path of *three* ready rows, and discovering it inside the first theorem wave
would mean re-cutting that wave and re-elaborating the prelude's consumers.

## 5. Porting order (one set = one mathematical story)

The def-import DAG fixes the order; each level is one work order.

| set | modules (home) | pin lines | depends on |
|---|---|---:|---|
| **D0** | `RepTheory/ContinuousSMulDiscrete`, `Adelic/Basic`, `Adelic/LsXi`, `Adelic/ConstantTerm` | 230 | mathlib only |
| **D1** | `AdelicHaar/{Local,Adele,GeneralLinear}` (absorbs `Topology`) | 205 | mathlib only |
| **D2** | `RepTheory/SmoothVectors` | 321 | D0 |
| **D3** | `AdelicLevel/{IdealBall,Projections,Level,HeckeGen}` (grows `Projections`; promotes `continuous_glMap`) | 813 | D1 |
| **D4** | `Adelic/CarrierPins`, `Adelic/RightConvolution`, `Adelic/FactorizableTestFn` | 179 | D1, D3 |
| **D5** | `Adelic/AutomorphicFn`, `Adelic/SmoothAutomorphicFn` | 161 | D2, D3, D4 |
| **D6** | `Adelic/WindowedSiegel/{Set,RowIsometry}` | 517 | D3, D4 |
| **D7** | `Adelic/ArchType` | 189 | D6 |
| **H1** | `Adelic/TestFnNearIdentity` (public shared prelude) | ≈400 once | D0–D7 |
| **T1** | the three `rightConv_ne_zero_of_*` headlines + `TestFnTop` | — | H1 |

Two ordering notes. `ArchType` lands last because the pin defines `archRowIsometryAt`
over the row-isometry subgroup of D6; the port keeps that edge rather than re-rooting the
predicate. And `HeckeGen` is the one genuinely new piece of mathematics in D3 — before
D3 is dispatched, scout it in a gitignored `Scratch.lean` (playbook §2.6): the
`localUnit`/`uniformizer`/`heckeGenAt` restricted-product manipulation is the only place
the pin does real work rather than transcription.

Reuse first, per set: `FactorizableTestFn` (D4) is already whole — only its import and
home move. `Projections` (D3) already carries 13 of its declarations. Everything else is
new. Run the statement checker after each set; a definition file closes green and freezes.

## 6. Verification and wiring

- **Checker.** Append each pin `Definitions/Def_*` to `SOURCES` and each new port module
  to `PORT_FILES` (both last, playbook §4). `Def_NumberField_AdelicHaar`,
  `Def_NumberField_AdelicLevel` and `Def_AutomorphicForm_FactorizableTestFn` are already
  listed; the other eleven pin files are new entries. The `identical` count should rise by
  the new public surface (pin-private matches verify through the dotted fallback and show
  as `promoted`); reconcile the before → after delta exactly. Run the one-token mutation
  test on one headline per set.
- **Consumer.** Extend `spec/AutomorphicFormConsumer.lean` with a real executed zone per
  level — a concrete instantiation, not `#check`. The existing Zone 1 is four `#check`s
  and should be replaced: `example`s that `rfl`-prove `adeleArch_apply`, that exhibit
  `1 ∈ levelOne ⊤` and `levelOne N ≤ levelZero N`, that `rightConv φ 0 = 0`, that
  `IsRowIsometry 1`, and that a compactly-supported locally-constant function is a smooth
  vector. Zone 3's headline application stays. Deleting any one module must break the
  consumer. H1 gets its own zone: a `TestFnNearIdentity.testFn` is a factorizable test
  function, with the near-identity support statement executed.
- **Axioms.** `#print axioms` on the non-`rfl` headlines (`isHaarMeasure_adelicGLHaar`,
  the compactness lemmas, `levelOne_le_levelZero`, the row-isometry invariance lemmas):
  expect `[propext, Classical.choice, Quot.sound]` (`uniformizer` uses `Classical.choose`).
- **Faithfulness.** Transcribe every `def`/`abbrev` taking type arguments in the pin's
  `variable … in`/section form (playbook §4): the checker sees text and reports
  `MISMATCH` otherwise. Header prose in `/- … -/` blocks only.

## 7. Budget and risks

Structural sum **2,544 pin lines / 314 declarations**; minus the 208 lines already
present (one whole module plus two slices, of which `Projections` grows by ~30) →
**≈2.3k new pin lines**, **≈2.9–3.4k written** at the port's 1.25–1.45 ratio for
definition-heavy modules. H1 adds one ≈400-line public prelude that replaces ≈705 lines
of duplicated block across the family (net ≈−300 once the three headlines land). No other
dedup saving is expected: the definition layer is definitions, not repeated proofs.

| # | risk | mitigation | state |
|---|---|---|---|
| 1 | `MeasurableSpace`/`BorelSpace` instance diamonds around `glBorel`/`adeleBorel` (reducible defs plus `BorelSpace` instances, on top of the port's `T2Space` instances) | transcribe the pin's local `letI`/`haveI`; build `Local` → `Adele` → `GeneralLinear` in order | open |
| 2 | mathlib drift `v4.33.1` → `v4.34.0` in `AdeleRing`/`InfiniteAdeleRing`/`RestrictedProduct`/`Matrix.GeneralLinearGroup` | the two landed slices already adapted; per-module `lake env lean` before the set build | open, expected cheap |
| 3 | `HeckeGen` restricted-product proofs | scout in `Scratch.lean`; budget the set separately | open |
| 4 | pin `private` helpers re-derived per consumer → duplication | each `Def_` node lands whole; H1 homes the one repeated prelude; consumer-local adapters stay `private` | designed away |
| 5 | statement drift on `def`s with section variables | pin `variable … in` form; checker per module | designed away |
| 6 | H1 namespace/name pollution (generic names `E`, `R`, `fa`, `ff`) | keep them under the prelude's own namespace, not top-level; only `AutomorphicForm`-qualified | designed away |

## 8. Recorded negatives (mathlib-first audit)

Searched mathlib `v4.34.0` (`.lake/packages/mathlib`) for the new material; all absent, so
each is a genuine port rather than a substitute: `ContinuousSMulDiscrete`, `IsSmoothVector`
/ `smoothVectors`, `adelicGLHaar` / `adelicAddHaar` / `glBorel`, and
`IsLevelOneMatrix` / `finiteLevelOne`. The base types `AdeleRing`, `InfiniteAdeleRing`,
`FiniteAdeleRing` and `Matrix.GeneralLinearGroup` are mathlib's and are adopted as the
interface from the first declaration (the landed `Projections`/`FactorizableTestFn` do
exactly this).

## 9. Reproduce

```bash
cd tools/deps
# the target's definition closure and status
python3 explore.py AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant
# the frontier row this foundation serves
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0
# the family prelude of §4.2 (43 shared names / ~705 removable lines)
python3 port_advise.py --target 'P2M/Sol/S_AutomorphicForm_exists_isFactorizableTestFn_*' --no-siblings
# price each edit in wave R / the D3 promotion
python3 build_ladder.py --edit FLTForHuman/AutomorphicForm/Gamma0FundamentalSet.lean
python3 build_ladder.py --edit FLTForHuman/NumberTheory/AdelicLevel/Projections.lean
cd ../lean
timeout 300 python3 spec/check_flt_statements.py
flock .lake/flt_build.lock timeout 900 lake build
```
