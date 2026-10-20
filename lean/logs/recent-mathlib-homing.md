# Homing the recent mathlib-shaped ports (2026-10-19/20)

> The durable statement of the problem, the criterion, the trade-offs and the namespace standard is
> [../topics/TOPIC-mathlib-module-homing.md](../topics/TOPIC-mathlib-module-homing.md); this file is
> the measured record and the list of what is not yet fixed. The residue of §3 is scheduled, module
> by module, in [../topics/TOPIC-mathlib-module-homing.md](../topics/TOPIC-mathlib-module-homing.md)
> §8 (landed 2026-10-20) — that section owns the target homes, the namespace map and the acceptance
> gates; this file stays the measurement of what the first pass did.

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

**Path right, namespace was a pin engine name (re-homed 2026-10-20; [../topics/TOPIC-mathlib-module-homing.md](../topics/TOPIC-mathlib-module-homing.md) §8):**
`P2MKcIgusaGroup` (`Algebra/AddAut/TransvectionFrame`), `P2MKcOrbitCensus`
(`GroupTheory/GroupAction/OrbitCensus`), `P2MKcMarksA4` (`GroupTheory/GroupAction/OrbitCounts`),
`P2MKcCB`/`P2MKcADAPT` (`Algebra/Module/Torsion/Coordinates`), `M4aP3B.Rows`/`Ws50CH3`
(`Analysis/Calculus/SeminormBound` + `Analysis/SpecialFunctions/Pow/Decay`, `Topology/Algebra/LocallyConstantCompactSupport`), `A2HexPoisson`
(`Analysis/Theta/HexagonalLattice`), `IBPLattice` (`Analysis/Fourier/FundamentalDomainIntegration`),
`AdjoinExt` (`FieldTheory/AdjoinExtension`), `TrDesc`/`TrFrob`/`TrFinal`
(`LinearAlgebra/Matrix/SimultaneousEigenbasis`), `Ef8d`
(`LinearAlgebra/FinrankStableInequality`), `RS40E`/`PPSeries43`
(`NumberTheory/LSeries/AnalyticContinuation`), `K2Seam3` (`NumberTheory/SquarefreeValues`),
`M4aP1R` (`NumberTheory/UnimodularLift`), `ChevalleyHom`
(`RingTheory/Valuation/ChevalleyExtension`), `CardC0` (`NumberTheory/ZModPowerTsum`),
`SolIntClosDVR` (`RingTheory/IntegralClosure/CompleteDVR`), `EngineCoreSol`/`RankOneNilSol`
(`RingTheory/LocalRing/{DimensionOne,IdempotentLift}`), `WittLift` (`RingTheory/WittVector/Lift`), `P2mLogBranch`/
`RedIntClosure` (`Analysis/Complex/LogBranchAndPrimitiveRoot`). These are FLT's names for objects
mathlib lacks ("keep FLT's where it does not"), in paths that already were their subjects. The
rehoming pass then renamed them to the object's namespace (or to a subject aux namespace:
`GroupTheory.MarksTwelve`, `LSeries.Abscissa`, `ZMod.BernoulliTsum`, `Matrix.TransposeMulVec`); the
seven older ones remain a separate campaign.

**Path and namespace both right (as surveyed; the rehoming pass later moved several to a
subject directory — `IsAddCyclicSquarefree` → `GroupTheory/SpecificGroups/CyclicSquarefree`,
`BrauerNesbittRepresentation` → `RepresentationTheory/BrauerNesbitt`,
`CompactOperatorFiniteDimensional` → `Analysis/Normed/Operator/`,
`StarSubalgebraIntegral` → `Topology/ContinuousMap/`, `FourierIntegralFlip` →
`Analysis/Fourier/VectorIntegralFlip`, `ClassGroupSupport` → `RingTheory/ClassGroup/Support` — their
namespaces were already right):** `Algebra/{IsAddCyclicSquarefree,FunctionSeparation,
BrauerNesbittRepresentation}`, `Analysis/{CompactOperatorFiniteDimensional,StarSubalgebraIntegral,
FourierIntegralFlip,MatrixGroup/*}`, `FieldTheory/TranscendentalAdjoin`,
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

## 7. The rehoming pass (2026-10-20)

The residue of §3 was scheduled in
[../topics/TOPIC-mathlib-module-homing.md](../topics/TOPIC-mathlib-module-homing.md) §8 and landed
the same day, all five waves: the 45 supplements were re-homed and namespace-rectified
(21 modules lost their pin labels — 302 declarations; the two that name their subject, `ChevalleyHom`
and `A2HexPoisson`, kept theirs), three mixed-subject modules were split (`TorsionFinite`,
`DecayEstimates`, `LocalRingNilpotent`), the dependency inversion of §3 was broken
(`FreeProduct` no longer imports `ModularForms/Analytic/PeterssonCoset`; the pin's five-line
`det_entries` is restated `private` there), and the module headers record where each pin namespace
went.

Measured: **845 `ok` + 7 `own`, 0 mismatch / 0 missing / 0 kw** over the 49 files that now carry the
45 modules (872 verdicts before; the 20-verdict delta is 19 privated declarations — `main`,
`_impl`, `gate_*`, `_proved` and `isIntegral_apply` — and one deduplicated `mul_apply'`); whole wired tree **3,486 ok / 0 / 0 /
11 own / 0 kw over 133 modules** (3,506 over 130 before; the three extra modules are the splits).
Dependency metric **845 modules / 1,954 edges / 434 cross-area** (842 / 1,955 / 436 before), and no
supplement imports an FLT-domain module. The decisions taken where the plan's table moved — the
namespace-shadowing fallbacks, the root `UnimodularLift`/`FinrankStable`, the private local
`det_entries`, the dropped cosmetic `PoissonSummation/` split — are recorded in that note's §8.11.

The seven older pin-code namespaces (`M4aS4`, `M4aLocalCFT`, `M4aHerbrand`, `P2MKcSerreTate`,
`P2MKcCQJvc`/`P2MKcCQJbc`) and the 24-window FLT-domain ones (`HeckeCharacter/Equality`,
`ModularForms/CohCarrier/TorsionOrbit`, …) are untouched: those modules are not supplements.
