# Homing the recent mathlib-shaped ports (2026-10-19/20)

> The durable statement of the problem, the criterion, the trade-offs and the namespace standard is
> [../topics/TOPIC-mathlib-module-homing.md](../topics/TOPIC-mathlib-module-homing.md); this file is
> the measured record and the list of what is not yet fixed.

**Manager's pass, 2026-10-20.** Prompted by two visible mismatches — a `Combinatorics/SimpleGraph`
module whose declarations were mostly `GroupTheory.GraphTransversal`, and `LinearAlgebra/Matrix`
modules whose declarations were `ModularCurve.ModularGroupPingPong` — this is the survey of the 93
Lean files added since 2026-10-19, the criterion the pass applies, what changed, and the dependency
measurement that validates it.

## 1. The criterion

1. **Home = the mathematical subject.** A module sits in the area of the mathematics it proves.
   A generic theory that needs no new theory from another area gets its **own** subject home, not
   the citer's; a theory that depends on a new theory from another area stays with that theory.
   Depending on a mathlib *library* (`SimpleGraph`, `Matrix`, …) is not such a dependency.
2. **Declaration namespace = the object's namespace where mathlib has one**, otherwise FLT's name
   *if it already names the subject*; prefer the aligned pin namespace (do not rename gratuitously).
3. **A pin `P2MW.S_<stem>` wrapper is scaffolding, not a namespace**, and is removed at the module
   boundary.
4. **A façade** (engine + headline modules) was a frozen-checker device for a small listed delta;
   `spec-pin:` + `check_port` make it unnecessary. It survives only if build granularity or a
   stable consumer API pays for it; otherwise merge.

## 2. The two motivating cases

* `Combinatorics/SimpleGraph/Transversal.lean` — 7 of the 9 prelude declarations mention
  `SimpleGraph`/`T.Adj`/`T.Walk`/`IsChain`; `IsConnectedTransversal` bundles `WalkConnected T D`
  with orbit conditions; only `eq_of_mem_orbit_sUnion`/`eq_of_mem_orbit_insert` are pure orbit
  lemmas, and they are proof-local. **Graph theory**, not generic group theory: stays in
  `Combinatorics/SimpleGraph`, namespace `SimpleGraph.GraphTransversal`; the eleven
  `orbitRepr`/`transl` declarations the Kurosh engine carried were graph theory too and moved here.
* `LinearAlgebra/Matrix/SpecialLinearGroupFreeProduct.lean` and
  `...FreeGenerators.lean` — Bass–Serre/free-product group theory; the fact that the object is a
  matrix group does not make the subject linear algebra. Moved to `GroupTheory/`; namespaces
  `ModularGroup.PingPong` and `Matrix.SpecialLinearGroup.*` (the objects).
* `LinearAlgebra/Matrix/SubfieldBasis.lean` — representation theory (a basis whose trace/det lie in
  a subfield); moved to `RepresentationTheory/SubfieldBasis.lean`.

## 3. Survey of the 93 recent files

**Path right, wrapper namespace (fixed):** `RepresentationTheory/{Burnside,CompactGroup,
InvariantPairing,SubrepresentationExtension}.lean` and `Analysis/Fourier/PoissonSummationPi.lean`
(`P2MW.S_…` removed; the inner `Representation.*`, `PiPoissonSummation.*`, `SchwartzMap.*` names
are the real API), `RepresentationTheory/SubfieldBasis.lean` (wrapper removed and its pin engine
namespace `P2mWs11Desc` renamed to `Representation.SubfieldBasisAux`).

**Path wrong (fixed by moving):** the two Matrix modules above; `SubfieldBasis`.

**Path right, namespace is a pin engine name (left for a later descriptive pass):**
`P2MKcIgusaGroup` (`Algebra/AddAutTransvectionFrame`), `P2MKcOrbitCensus`
(`Algebra/FunctionOrbitCensus`), `P2MKcMarksA4` (`Algebra/MulActionOrbitCounts`),
`P2MKcCB`/`P2MKcADAPT` (`Algebra/TorsionByCoordinates`), `M4aP3B.Rows`/`Ws50CH3`
(`Analysis/DecayEstimates`, `Topology/Algebra/LocallyConstantCompactSupport`), `A2HexPoisson`
(`Analysis/Theta/HexagonalLattice`), `IBPLattice` (`Analysis/FundamentalDomainIntegration`),
`AdjoinExt` (`FieldTheory/AdjoinExtension`), `TrDesc`/`TrFrob`/`TrFinal`
(`LinearAlgebra/Matrix/SimultaneousEigenbasis`), `Ef8d`
(`LinearAlgebra/FinrankStableInequality`), `RS40E`/`PPSeries43`
(`NumberTheory/LSeries/AnalyticContinuation`), `K2Seam3` (`NumberTheory/SquarefreeValues`),
`M4aP1R` (`NumberTheory/UnimodularLift`), `ChevalleyHom`
(`NumberTheory/ValuationSubring/ChevalleyExtension`), `CardC0` (`NumberTheory/ZModPowerTsum`),
`SolIntClosDVR` (`RingTheory/IntegralClosureCompleteDVR`), `EngineCoreSol`/`RankOneNilSol`
(`RingTheory/LocalRingNilpotent`), `WittLift` (`RingTheory/WittVectorLift`), `P2mLogBranch`/
`RedIntClosure` (`Analysis/Complex/LogBranchAndPrimitiveRoot`). These are FLT's names for objects
mathlib lacks ("keep FLT's where it does not"), in paths that already are their subjects; a
descriptive rename is a separate campaign.

**Path and namespace both right (no change):** `Algebra/{IsAddCyclicSquarefree,
FunctionSeparation,BrauerNesbittRepresentation}`, `Analysis/{CompactOperatorFiniteDimensional,
StarSubalgebraIntegral,FourierIntegralFlip,MatrixGroup/*}`, `FieldTheory/TranscendentalAdjoin`,
`GroupTheory/ExactFundamentalDomain`, `LinearAlgebra/{Dual/EvalSpan,Matrix/SL2Generation,
Matrix/SpecialLinearGroupHermite}`, `RepresentationTheory` (post-wrapper), `RingTheory/
DedekindDomain/ClassGroupSupport`, `Topology/…`.

## 4. What changed

* `Combinatorics/SimpleGraph/Transversal.lean`: `GroupTheory.GraphTransversal` →
  `SimpleGraph.GraphTransversal`; the eleven graph declarations moved in from the Kurosh engine
  (the module now wires both pin files, 21 ok).
* `GroupTheory/BassSerre/{CosetGraph,MinimalPeriod}.lean` (from `GroupTheory/CoprodI/`):
  one `GroupTheory.BassSerre` namespace (the pin's, aligned) across both; the edge-chain engine
  merged into it.
* `GroupTheory/ModularGroup/FreeProduct.lean` (from `LinearAlgebra/Matrix`): `ModularGroup.PingPong`.
* `GroupTheory/FreeGroup/KuroshRank.lean` stays the engine (104 ok); the four
  `Matrix.SpecialLinearGroup` headlines live in `GroupTheory/FreeGroup/SpecialLinearGroupGenerators.lean`
  (52 ok) — restored as the **user-facing API module** after the user-view review. The old
  `LinearAlgebra/Matrix` façade was not kept *as a façade* (the checker needs none), but the user's
  natural import path for the `SL₂` results is a module named for them, not the Kurosh engine.
* `RepresentationTheory/SubfieldBasis.lean` (from `LinearAlgebra/Matrix`); wrapper namespaces
  stripped from it and the four representation modules.
* `Analysis/Fourier/PoissonSummationPi.lean`: the `P2MW.S_…` wrapper is gone; the headline's
  proof had to qualify `WithLp.toLp`/`WithLp.ofLp` (the unqualified spellings resolved only with
  the wrapper's namespace stack), and the seven `own:` markers for the `LocSum` deviation were
  re-keyed from `P2MW.S_….PiPoissonSummation.*` to `PiPoissonSummation.*` in
  `spec/decl_markers.tsv`. Checker: 31 ok / 0 mismatch / 0 missing / **7 own** (the registered
  `LocSum` deviation).
* `RepresentationTheory/SubfieldBasis.lean`: the pin engine namespace `P2mWs11Desc` is now
  `Representation.SubfieldBasisAux`; checker 17 ok.

## 4b. Where the pin-code namespaces actually are

A scan of the whole port finds 31 files carrying a pin-code namespace. **24 of them are in the
2026-10-19/20 waves** (the modules just ported: `Algebra/{AddAutTransvectionFrame,
FunctionOrbitCensus,MulActionOrbitCounts,TorsionByCoordinates}`, `Analysis/{DecayEstimates,
FundamentalDomainIntegration,Theta/HexagonalLattice,Complex/LogBranchAndPrimitiveRoot}`,
`FieldTheory/AdjoinExtension`, `HeckeCharacter/Equality`, `LinearAlgebra/{FinrankStableInequality,
Matrix/SimultaneousEigenbasis}`, `ModularForms/CohCarrier/TorsionOrbit`,
`NumberTheory/{LSeries/AnalyticContinuation,SquarefreeValues,UnimodularLift,
ValuationSubring/ChevalleyExtension,ZModPowerTsum}`, `RingTheory/{IntegralClosureCompleteDVR,
LocalRingNilpotent,WittVectorLift}`, `Topology/Algebra/LocallyConstantCompactSupport`); **7 are
older** (`M4aS4` in `NumberTheory/AdelicHaar/{AdelicModulus,PlaceMeasure}`,
`M4aLocalCFT` in `FujisakiCompact`, `M4aHerbrand` in `IdeleClass/{Vocab,ArchSemilocal}`,
`P2MKcSerreTate` in `InertiaReduction`, `P2MKcCQJvc/CQJbc` in `CyclicQuotientJ`). They are the
pin `S_` files' generated names copied with the transcription — provenance is the pin, not the
age of the module — and the modules affected by this pass (the two above) are fixed.

## 5. Verification

Per module: `lake build`, 0 warnings; `check_port --force` 0 mismatch / 0 missing (graph 21,
FreeDoubleCoset 12, CosetGraph 49, MinimalPeriod 75, KuroshRank 104, SpecialLinearGroupGenerators 52, FreeProduct 68,
QExpansionCoeff 19, SubfieldBasis 17, representations 1 × 4); axioms unchanged on the headlines
that were re-checked.

**Dependency metric** (whole tree, `import FLTForHuman.*` edges): baseline `8cd8e96` — 841
modules / 1,954 edges / 439 cross-area; after — 842 / **1,955** / **436**. The new
`ModularForms/HeckeFrickeTrace.lean` is +1 module/+1 edge of that delta, so the re-home plus the
user-facing API module is **even on edges** and three cross-area edges down. The manager's acceptance
condition (dependencies down or even) is met.

## 6. Reproduce

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/Combinatorics/SimpleGraph/Transversal.lean
python3 spec/check_port.py --force FLTForHuman/GroupTheory/FreeGroup/KuroshRank.lean
python3 spec/check_port.py --all
```
