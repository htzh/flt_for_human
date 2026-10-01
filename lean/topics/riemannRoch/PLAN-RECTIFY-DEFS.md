# Plan — `Defs/` rectification and the ℙ¹ core breakout

**Status: R1 executed (§5.1); R2 deferred; `Defs/P1.lean` decided but deferred (§7).**
Written 2026-09-30 when the P3.2 port paused. This is a **rectification plan**, not a
port: it decides *homes*, not mathematics. It gates the resumption of the row-2 tails
(§2 of [HANDOFF-P3-2.md](HANDOFF-P3-2.md)) and rows 3.3–3.7, because a consumer that
needs only the definitions must not import the proof theory.

Read [WORKFLOW.md](WORKFLOW.md) first. This note assumes its round discipline
(measured moves, one refactor-shaped pass, one whole-tree build, checker re-run).

## 0. The rule, and why now

**Rule (human, 2026-09-30).** `Defs/` holds the **public API definitions**. A module
whose weight is proofs must not live there. **Two exceptions** keep a lemma in a
`Defs/` file:

1. it is *commonly used by consumers to adapt the definitions* (a short law such as
   `evalAt_mul`, named from several modules); or
2. it is a definitional identity (`rfl` bridges such as `dCoord_eq`, `dX_def`).

"Commonly used" is decided by cross-module citation, not by taste.

**Why pay now.** Measured from `tools/deps/port_graph.json` + `build_ladder.py --edit`
(2026-09-30). The theory blobs are today's cheap edits; the low-level def modules are
already expensive:

| theory-in-`Defs` file | ln | def-like | thm | transitive dependents | cascade now |
|---|---:|---:|---:|---:|---:|
| `Defs/P1ResidueCore.lean` | 6,471 | 44 | 306 | **0** | ≈78 s |
| `Defs/CanonicalLocalResidueInstanceV2.lean` | 1,695 | 33 | 88 | 2 | ≈113 s |
| `Defs/P1Dictionary.lean` | 1,345 | 4 | 75 | 1 | ≈94 s |
| `Defs/LocalResidueCalculus.lean` | 1,230 | 0 | 35 | 1 | ≈92 s |
| `Defs/PlaceEvaluationAlgebra.lean` | 186 | 0 | 16 | 2 | small |
| `Defs/Place.lean` | 393 | 9 | 36 | **56** | ≈341 s |
| `Defs/Divisor.lean` | 91 | 9 | 6 | 52 | large |
| `Defs/PushPull.lean` | 757 | 19 | 49 | 33 | large |

Once 3.2's sibling tails and rows 3.3–3.7 land, `P1ResidueCore`'s fan-in stops being
0 and the same edit becomes a whole-tree cascade. **R1 below is the cheap,
isolated cut; R2 is the expensive generic cut and may be deferred.**

**Tool note.** No planning tool is built for this round: the moves are isolated, so
ordering is trivial. If a home-adviser is wanted later it should be built *against the
pin* (a pre-port `port_advise.py` extension that reads `Def_*`/`Thm_*`/`S_*` and
proposes homes before a line is written), not as a post-mortem over the port. Recorded
here so the idea is not lost.

## 1. Target directory scheme

Module paths are **homes**, not namespaces: namespaces stay `AlgebraicCurve`,
`AlgebraicCurve.Place`, `RationalFunctionField`, … unchanged, so the statement checker
is unaffected by a move except for the `PORT_FILES` path.

| home | role | status |
|---|---|---|
| `AlgebraicCurve/Defs/` | public API **definitions + adapter lemmas only** | keep, prune |
| `AlgebraicCurve/P1/` | ℙ¹-specific theory (dictionary, residue core) | **new** |
| `AlgebraicCurve/Place/` | generic place/valuation theory (over-DVR, dictionary, push-pull, correspondence, semilinear, completion) | **new** |
| `AlgebraicCurve/LocalResidue/` | the generic canonical-local-residue construction and calculus | **new** |
| `AlgebraicCurve/Adeles/` | adelic index, repartitions | **new** |
| `AlgebraicCurve/Canonical/`, `Genus/`, `PrincipalDivisors/`, `RiemannRoch/`, `WeilExchange/`, `IsCurveOver/` | existing subject dirs | keep |

Precedent: `ModularForms/WeightOne/Defs/` is the subject-local defs subpackage, and
[../hecke/TOPIC-weightone-rectify.md](../hecke/TOPIC-weightone-rectify.md) is the
cost-of-doing-it-late post-mortem this plan avoids.

## 2. Per-declaration classification

Every declaration in a candidate file gets one verdict; the round's `WORKORDER` carries
the table.

| verdict | meaning | home |
|---|---|---|
| `KEEP-DEF` | def-like, part of the API (externally cited, or needed to state the API) | `Defs/` |
| `MOVE-DEF` | def-like but internal to the theory (only its own module's proofs use it) | travels with the theory |
| `ADAPTER` | short theorem/lemma named from ≥2 modules, statement over API defs only | `Defs/` (exception 1) |
| `THEORY` | everything else theorem/lemma-shaped | subject dir |
| `INSTANCE-PRODUCER` | an `instance`; its proof is on the import path, so it cannot be split from its module | subject dir, documented |
| `SCAFFOLD` | empty audit sections, `#check`/`example` probes, duplicated private helpers | delete |

`INSTANCE-PRODUCER` matters: `spec/RiemannRochConsumer.lean` ZONE F imports
`CanonicalLocalResidueInstanceV2` to get `HasCanonicalLocalResidueKStar` by
`inferInstance`. The instance's *construction* stays on that import path; only its
**data defs** (`uniformizerSubring`, `poleSubmodule`, `laurentTailCoeff`, …) are
separable.

A `def` is only hoistable into `Defs/` if its **body** cites only already-homed
declarations. This is the one check that makes the split mechanical.

## 3. Current `Defs/` files: disposition

`ln` / `defs` / `thms` and dependents are the §0 measurements. `in-file defs` names the
declarations that stay in `Defs/` (the rest move with the theory or are re-homed).

### 3.1 Theory blobs — R1 (isolated, do first)

| current file | ln | verdict | target theory home | in-file defs |
|---|---:|---|---|---|
| `Defs/P1ResidueCore.lean` | 6,471 | split | `P1/*` (§4) | the `P1*` API defs → `Defs/P1.lean` |
| `Defs/P1Dictionary.lean` | 1,345 | MOVE | `P1/Dictionary.lean` | `placeOfPoint`, `principalDivisor`, `placeEquivOption` → `Defs/P1.lean` |
| `Defs/CanonicalLocalResidueInstanceV2.lean` | 1,695 | MOVE | `LocalResidue/Instance.lean` | `uniformizerSubring`, `simplePoleSubmodule`, `simplePoleResidueAux`, `poleSubmodule`, `laurentTailCoeff`, `higherPoleCorrection`, `canonicalLocalResidueDataKOfExtend`, `CanonicalLocalResidueDataS`, `CoefficientFieldSection`, `Lg37CompletionSection` → `Defs/LocalResidue.lean` |
| `Defs/LocalResidueCalculus.lean` | 1,230 | MOVE | `LocalResidue/Calculus.lean` | none (0 defs) |
| `Defs/PlaceEvaluationAlgebra.lean` | 186 | **decide** | keep in `Defs/` *or* `Place/EvaluationAlgebra.lean` | the adapter laws |

`PlaceEvaluationAlgebra` is the designed test of exception 1: its 16 lemmas are the
`evalAt`/`evalFun` laws the ℙ¹ dictionary consumes to *use* the `PlaceEvaluation`
defs. **Recommendation: keep in `Defs/`**, and let the work order record which of the
16 are cited from ≥2 modules (keep those) and which are single-consumer (move).

### 3.2 Generic/mixed files — R2 (high fan-in, one bounded pass)

| current file | ln | defs/thms | verdict | target theory home | in-file defs |
|---|---:|---|---|---|---|
| `Defs/Place.lean` | 393 | 9/36 | split | `Place/Ord.lean` (the ord/comap theory) | `Place`, `ResidueField`, `deg`, `FiniteResidue`, `heightOneSpectrum`, `adicValuation`, `ord`, `ofHeightOneSpectrum` |
| `Defs/PlacesOverDVR.lean` | 449 | 9/31 | split | `Place/OverDVR.lean` | `integralClosureAt`, `fiberCenter`, `fiberEquiv`, `fiberOver` |
| `Defs/PlaceDictionary.lean` | 399 | 5/12 | MOVE | `Place/Dictionary.lean` | the centre/inertiaDeg defs |
| `Defs/PushPull.lean` | 757 | 19/49 | split | `Place/PushPull.lean` | `Place.restrict`, `pullback`, `pushforward`, `ramificationIndex`, `inertiaDeg`, `Pic0` homs |
| `Defs/Correspondence.lean` | 406 | 16/26 | split | `Place/Correspondence.lean` | `algebraAlong`, `*Along` predicates, `correspondence` |
| `Defs/SemilinearAut.lean` | 222 | 7/20 | split | `Place/SemilinearAut.lean` | `SemilinearAut`, its `Place`/`Divisor` actions |
| `Defs/PlaceCompletion.lean` | 552 | 18/16 | split | `Place/Completion.lean` | the completion-comap defs |
| `Defs/AdelicIndex.lean` | 443 | 24/44 | split | `Adeles/Index.lean` | `adeleSpace`, `adeleBddPrincipal`, `LSpace`, `ell`, `H1` |
| `Defs/Repartitions.lean` | 158 | 6/13 | split | `Adeles/Repartitions.lean` | the repartition defs |
| `Defs/WeilOfKaehler.lean` | 360 | 5/19 | split | `LocalResidue/WeilOfKaehler.lean` | `weilOfKaehler`, `ResidueTheorem` |
| `Defs/RatFuncPlaces.lean` | 273 | 5/15 | split | `P1/Places.lean` | `finitePlace`, `placeInfty`, the residue-degree defs |
| `Defs/CanonicalDivisor.lean` | 153 | 10/12 | split | `Canonical/CanonicalDivisor.lean` | `HasCanonicalDivisor`, `dCoord`, `uniformizer` |
| `Defs/IsCurveOver.lean` | 87 | 4/6 | split | `IsCurveOver/Defs.lean` | the `IsCurveOver` class and its fields |
| `Defs/LocalResidue.lean` | 332 | 13/22 | split | `LocalResidue/Interface.lean` | `LocalResidueData`, `CanonicalLocalResidueDataK`, `HasLocalResidue`, `HasCanonicalLocalResidueK`, `HasCanonicalLocalResidueKStar`, `HasSeparableResidue` |

### 3.3 Keep as definitions — R3 (verify only)

| current file | ln | defs/thms | note |
|---|---:|---|---|
| `Defs/Divisor.lean` | 91 | 9/6 | `Divisor`, `Pic0`, `degree`; the 6 lemmas are adapter-shaped |
| `Defs/PlaceEvaluation.lean` | 105 | 5/9 | the interface + its adaptation laws |
| `Defs/PoleDivisorPackage.lean` | 109 | 10/0 | pure defs |
| `Defs/RiemannRochRows.lean` | 74 | 6/2 | pure defs |
| `Defs/RegularDifferentials.lean` | 55 | 1/2 | tiny |
| `Defs/CanonicalDivisorUniformizer.lean` | 37 | 0/1 | the `rfl` identity `dCoord_eq` |
| `Defs/IntegralAdjoin.lean` | 96 | 0/3 | **flag**: pure theory, but a tiny shared prelude — keep or move to `Place/Prelude.lean` |
| `Defs/KaehlerTranscendental.lean` | 95 | 0/3 | **flag**: pure `FF2` Kähler theory; candidate `AlgebraicCurve/Kaehler/` |

## 4. The ℙ¹ core breakout

`Defs/P1ResidueCore.lean` is 6,471 lines of 21 concatenated port chunks (~60
`section`s, ~350 declarations, one headline at the end). It must become a
`P1/` module family.

**Why a consecutive partition is safe.** Lean forbids forward references, so the
file's declaration order is already a topological order of its own dependency graph.
Partitioning the text into **consecutive** blocks, each importing the previous, cannot
break a backward reference and preserves every ordering constraint. Only a forward
reference would break, and the file has none by construction.

**Proposed modules** (grouped from the section names, in file order; sizes are current
line spans, to be re-measured after the generic blocks are peeled):

| # | module | covers |
|---|---|---|
| 1 | `P1/EnginePrelude.lean` | `FLT.EulerDualBasis`, `Place` restrict/ultrametric, `RationalFunctionField.PlaceInfty`, `EnginePrelude`, `P1NamedRows`, `P1Gates`, `RatFuncIntegrality`, `P1PolynomialSubrows`, `P1PrincipalPartSubrows`, `P1PartialFraction`, `GateResidue`, `OrdIntegrand` |
| 2 | `P1/Differential.lean` | `RationalFunctionFieldDifferential`, `NonVanishing`, `Place.Uniqueness`, `ResidueEngine` |
| 3 | `P1/UnitNormalForm.lean` | the `MilneAvAg9bRd15UnitNormalFormLaurentSeed` (`ag9b15u_*`) block |
| 4 | `P1/DXCoeff.lean` | `dX`, `NumDenom`, `PerPlace`, `Discharge` |
| 5 | `P1/DivisorAction.lean` | `Divisor.SmulAux`/`Pullback`/`Galois`, `Descent`, `SurjectivePlaceInfty`, `Bridge` → mostly `Place/`, split out |
| 6 | `P1/Wronskian.lean` | `WronskianBound`, `DXCoeff`, `FinitePlaces`, `PlaceInftySide`, `Glue`, `PrincipalPartAtoms` |
| 7 | `P1/UnitFinite.lean` | `UnitFinite`, `KaehlerRatFunc`, `PCoordinateIdentity`, `NamedHigherDeg`, `DegOneDischarge`, `AlgClosed` |
| 8 | `P1/FinitePlaceResidue.lean` | `ValuationSubring`, `DedekindModel`, `MOneSimplePoleBounds`, `TraceRow`, `FinitePlaceTrace`, `DerivativeRegular`, `LeibnizCore`, `BridgeDischarge`, `MonicRatioResidue` |
| 9 | `P1/PlaceInftyResidue.lean` | `MonicRatioReduction`, `ComposedEngineInfty*`, `PurelyTranscendentalSimple`, `TowerComposites`, `CanonicalLocalResidueKSimplePoleCoordIndep` |
| 10 | `P1/KaehlerResidue.lean` | `KaehlerToolbox`, `DXCoeffIntegrality`, `LemmaA`, `ExactDifferentialEngine`, `RatFuncClauses`, `PlaceInftyConsumers`, `AlgClosedDischarge` |
| 11 | `P1/PerfectField.lean` | `EulerPerfectField`, `DerivativeRegular`, `LeibnizCore`, `BridgeDischarge`, `TraceValue`, `LemmaAPerfect`, `ChainPerfect` |
| 12 | `P1/KernelEngine.lean` | `KernelEngine`, `SimplePoleSeam`, `SmulReduction`, `PerGenerator`, `Engine`, `AlgClosedDischarge`, `BridgeCorollary` |
| 13 | `P1/PerfectResidueEngine.lean` | `MOnePerfect`, `PerGenerator`, `EngineCharFree`, `AlgClosedAnyChar`, `ResidualLocation` |
| 14 | `P1/CharP.lean` | `CharFreeToolkit`, `CharPCartier`, `Headlines`, `Bc2Carrier` |
| 15 | `P1/Core.lean` | `placeInfty_eq_p1PlaceInfty`, the headline `trace_localResidue_placeInfty_X_pow_eq_zero` |

Target ≤ ~900 lines per module; modules 8 and 10 are the ones to subdivide further if
they stay over. Exact boundaries belong to the work order, with the invariant
**consecutive and linearly imported**.

**The API extracted to `Defs/P1.lean`.** The `def`-like declarations the downstream
rows state against, all of which have bodies over already-homed API and so hoist
cleanly:

- data: `P1PolynomialGenerators`, `P1PrincipalPartGenerators`,
  `P1PartialFractionGenerators`, `p1PrincipalPartAtom`, `dX`
- coordinate/rank: `kaehlerPolynomialBasis`, `kaehlerRatFuncBasis`,
  `ratFuncDXCoeff`, `KaehlerRankOne`, `RamificationInertiaIdentity`
- named rows (the pin's bespoke `Prop` objects): `P1DifferentialCoeffRegularFinite`,
  `P1DifferentialCoeffUnitFinite`, `CanonicalLocalResidueKDifferentialCoordIndep`,
  `CanonicalLocalResidueKSimplePoleCoordIndep`,
  `P1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg`,
  `P1FinitePlaceCanonicalResidueAtomMGeTwoTrace(+HigherDeg)`,
  `P1PrincipalPartMOneSimplePoleCancel`,
  `P1FinitePlaceSimplePoleResidueAdjoinRootValue`,
  `P1PlaceInftySimplePoleResidueEulerValue(+TopDeg/Monomial/X)`
- ℙ¹ places: `finitePlace`, `placeInfty`, `placeOfPoint`, `principalDivisor`,
  `placeEquivOption`, `finitePlaceResidueFieldAlgEquivAdjoinRoot`
- adapters (exception 1): `p1DifferentialCoeffRegularFinite_of_unitFinite`,
  `p1DifferentialCoeffUnitFinite_dX`, the `_def`/`rfl` identities

Not ℙ¹-specific and therefore hoisted to `Defs/LocalResidue.lean` instead:
`kaehlerResidueFunctionalK` (stated over `Place K F`).

**Cleanup in the same pass.** Remove the empty `section AxiomAudit(s) … end`
scaffolding and the `#check`/`example` probe blocks; resolve the five duplicated
private helpers and the ten `_s12` rows and the `differentialCoeff_add''` from
[HANDOFF-P3-2.md](HANDOFF-P3-2.md) §4; drop the deliberate duplication the
`P1Core`↔sibling-atom sharing left behind.

## 5. Order, waves, verification

The round is a **refactor-shaped pass** (WORKFLOW §8): existing modules are edited, so
it ends with **one whole-tree build**.

| phase | content | build price |
|---|---|---|
| **R0** | scaffolding cleanup (delete empty audits/probes, no import change) | per-module `lake env lean` only |
| **R1** | create `Defs/P1.lean`; split `P1ResidueCore` → `P1/*`; move `P1Dictionary` → `P1/`; move `Instance`/`Calculus` → `LocalResidue/`; decide `PlaceEvaluationAlgebra` | theory blobs have 0–2 dependents: ≈80–120 s each |
| **R2** | the generic/mixed table (§3.2) in one bounded pass | high fan-in: one whole-tree build |
| **R3** | checker wiring, consumer test, closeout | — |

R1 and R2 must not run concurrently on the same modules. If R2 is deferred, R1 alone
still unblocks rows 3.3–3.7 for the ℙ¹/residue cone, because the new `P1/` and
`LocalResidue/` modules import the existing generic `Defs/` homes unchanged.

Verification (the WORKFLOW §7 gate):

```bash
cd lean
python3 spec/check_flt_statements.py                       # 3642 / 0 / 0 / 30
flock /tmp/flt_for_human.lock timeout 300 lake build <each new module>
lake build                                                  # ONE whole-tree build, at the end
lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/RiemannRochConsumer.lean
python3 ../tools/check_math_delimiters.py ../lean/topics/riemannRoch/*.md
```

Plus: update `PORT_FILES` (rename, do not duplicate, path entries); statements are
**verbatim** — a move changes no statement, so the checker must stay at 3642 / 0 / 0 /
30; `.olean` mtimes confirm only the round's modules moved; no new `sorry`/`axiom`.

## 5.1 R1 as executed (landed 2026-09-30)

R1 was carried out by hand — the split is too delicate to delegate. Everything below
is verified on the live tree.

**Moved** (path only; namespaces and statements unchanged):

| from | to |
|---|---|
| `Defs/P1Dictionary.lean` | `P1/Dictionary.lean` |
| `Defs/CanonicalLocalResidueInstanceV2.lean` | `LocalResidue/Instance.lean` |
| `Defs/LocalResidueCalculus.lean` | `LocalResidue/Calculus.lean` |

**Split.** `Defs/P1ResidueCore.lean` (6,470 ln) is gone, replaced by a 15-module
linear chain under `P1/`: `EnginePrelude`, `Differential`, `UnitNormalForm`,
`DXCoeff`, `DivisorAction`, `UnitFinite`, `FinitePlaceResidue`, `TraceEngine`,
`Separating`, `Adjoin`, `PerfectPrelude`, `KaehlerIntegral`, `PerfectField`,
`PerfectResidue`, `Core`. Each imports the preceding slice, so building `P1/Core`
builds the chain. Cuts sit at nesting depth 1 (chunk starts) and depth 2 (namespace
resets), which keeps every slice balanced.

**Three cross-slice `private` helpers were promoted** to public — a `private` is
module-local, so a cut that separates a helper from its consumers forces promotion:
`Place.simplePoleResidueAux_mul_of_mem` and
`Place.mul_mem_simplePoleSubmodule_of_mem` (now visible from `P1/Separating`), plus
the generic `Place.differentialCoeff_add''`, promoted in
`LocalResidue/Calculus.lean` at the pin's implicit-`v` binder with the `P1`
re-landing deleted (the HANDOFF §4.4 fix). All three now match the pin's
`p2m_export`ed declarations.

**Verified:** `lake build` green (4,873 jobs, the round's one whole-tree build);
`python3 spec/check_flt_statements.py` → **3645 / 0 / 0 / 30** (135 promoted from
pin-private, +3 over the pre-round 3,642 / 132); `RiemannRochConsumer.lean` 0 errors;
hygiene clean. `PlaceEvaluationAlgebra` stays in `Defs/` under exception 1.

**Not done — the R1 remainder, the `Defs/P1.lean` API extraction — is deferred by
decision (§7.2), not blocked.** The rows are API; extracting them into `Defs/P1.lean`
is hygiene while no future consumer is known, and the ℙ¹-place defs (`finitePlace`,
`placeInfty`, `placeOfPoint`, …) are entangled with `Defs/RatFuncPlaces.lean`, an R2
item. The `P1/` modules are still a leaf, so it stays cheap whenever it is taken up.

## 6. WORKFLOW.md amendment

- header "Current state" → checker 3642 / 0 / 0 / 30; 3.2b–e landed; **paused for the
  definitions round**;
- §0 → add `PLAN-RECTIFY-DEFS.md` and the `AlgebraicCurve/{P1,Place,LocalResidue,Adeles}/`
  homes;
- §1 → name the two round-kinds (per-set port loop, cross-cutting definitions round);
- §8 → add **8.2 Definitions rounds**: the rule, the two exceptions, the classification
  verdicts, "pay it first";
- §9 → mark 3.2b–e done and insert the definitions round as the gate for 3.3–3.7.

## 7. Decisions (resolved by the human, 2026-09-30)

1. Directory names: `P1/` (done) and **`Place/`** (R2's generic theory home);
   `LocalResidue/` stands for the R1 calculus/instance; `Adeles/` for the R2 adelic
   files.
2. The bespoke `def … : Prop` atom/predicate rows are **API** — when extracted they
   go to `Defs/P1.lean`, not with the `P1/` theory. **The extraction itself is
   deferred** (see below): the defs now live in the `P1/` theory home, and since it
   is not clear future API consumers will exist, moving them into `Defs/` is hygiene
   rather than a known need. It stays cheapest now (R1 left `P1/` a leaf) if a
   consumer appears.
3. `PlaceEvaluationAlgebra` stays in `Defs/` under exception 1 (the adapter rule).
4. **R2 stays deferred** (its own bounded refactor round when taken up).
5. `IntegralAdjoin` and `KaehlerTranscendental` stay `Defs/` leaves for now; revisit
   only if they acquire consumers or R2 touches them.

Remaining cleanup (the §4 refactor-debt list, the empty audit scaffolding, the
`Defs/P1.lean` extraction) is deferred until a consumer or an issue makes it pay.
