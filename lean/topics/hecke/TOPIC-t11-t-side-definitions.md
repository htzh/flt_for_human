# Topic 11: the T-side definition layer

**Status: planned (not started).** Successor to T10 of
[../PORTING-Hecke.md](../PORTING-Hecke.md) and the first port of the T side of
$`R = T`$. It ports the definition layer only: the Galois substrate the T package
is stated against, the Hecke–Galois datum, the local Hecke algebra, the patching
vocabulary, and the three algebra theorems the local Hecke algebra pulls in. The
theorem layer above the definitions (the 24 `GaloisRep.DeformationRingData.*`
lemmas, the 18 `HeckeGaloisRepDatum.*` lemmas, the `PatchingDatum` exit and the
R≅T assembly) is a later topic.

**Mathematics.** [../../math/018-t-side-definitions.md](../../math/018-t-side-definitions.md)
explains every definition below in mathematical terms. Read it first; it is the
specification this work order implements.

**Measurements and context.** [../../studies/r-equals-t-in-the-proof-base.md](../../studies/r-equals-t-in-the-proof-base.md)
§6–§7 (the R=T route, the graph numbers, the port-scope reading).

**Audience.** A fresh session taking the T-side definition-layer port. Read, in
order: [porting-playbook.md](../../porting-playbook.md) (all of it; §7 for a
definitions layer, §3.11 and §4 for the build and drift discipline);
[../../math/018-t-side-definitions.md](../../math/018-t-side-definitions.md);
[../PORTING-Hecke.md](../PORTING-Hecke.md) §5; and the pin's `Definitions/Def_*`
files listed in §0.

**Build discipline — read this first.** Every build is bounded and a blow-up is
quarantined, not waited on. Measured with mathlib prebuilt: a green
`lake env lean <module>` of this size is **~4 s**, `lake build <module>` with
deps cached **~2–5 s**, and a `whnf`/heartbeat timeout at the default cap
**errors in ~15–20 s** — it does not hang. A healthy full `lake build` of this
tree is **seconds to about a minute**.

- Run every build under a hard bound: `timeout 60 lake env lean <file>`,
  `timeout 90 lake build <module>`, `timeout 180 lake build`. **A multi-minute
  build is never acceptable, not even while experimenting** — a fifteen-minute
  bound is a bug in the work order, not a licence to wait.
- **Expect ≤ 30 s.** Any single build past ~60 s must be treated as a blow-up
  and bisected, not watched; a bound that lets a build run to 15 minutes is
  itself the failure.
- **Quarantine immediately.** On a non-return, comment the declaration out and
  bisect, or reproduce in the gitignored `Scratch.lean` with
  `set_option diagnostics true` and a low cap (`set_option maxHeartbeats 20000`).
  Do not re-run the same file hoping for a different result.
- **Never raise `maxHeartbeats` (or `maxRecDepth`).** The cap already fails in
  under 20 s; raising it turns that into an unbounded wait. The usual causes are
  a `FunLike`-quantified lemma at a bare function type, or a concrete
  `IntermediateField` carrier defeq (see the two failure modes in the playbook).
- **Tell a blow-up from contention by CPU time.** Measure with `time` (or
  `/usr/bin/time -v`): high user CPU + timeout is a real blow-up (bisect);
  ~0 CPU wall-time is lock contention with another agent's build (re-run when
  idle; never build concurrently with another agent).

## 0. The cone

The import closure of the four T-side definition modules is 16 definition
modules / 1,755 pin lines. Five are already mirrored (523 lines) and contribute
only their names to `SOURCES`; the **new** work is the rest of the table.

| pin module | lines | decls | new? | pin imports |
|---|---:|---:|---|---|
| `Def_Algebra_PatchingDatum` | 44 | 9 | **new** | mathlib only (`MvPowerSeries`, `Ideal.Maps`, `Ideal.Operations`) |
| `Def_FLTPrelim_Modularity` | 106 | 19 | **partly** — the `qCoeff`/`IsNormalizedEigenform` half is ported; the `WeierstrassCurve` block is new (~60 lines, 10 decls) | mathlib |
| `Def_FLTPrelim_GaloisRep` | 83 | 11 | **new** | mathlib |
| `Def_FLTPrelim_FreyPackage` | 97 | 24 | **new** | mathlib |
| `Def_FLTPrelim_Ramification` | 52 | 4 | **new** | `FreyPackage`, `FLTPrelim_GaloisRep` |
| `Def_EllipticCurve_FrobeniusTrace` | 66 | 8 | **new** | `FLTPrelim_GaloisRep`, `FLTPrelim_Ramification`, mathlib |
| `Def_GaloisRep_Residual` | 105 | 14 | **new** | `FrobeniusTrace`, `FLTPrelim_Modularity`, mathlib |
| `Def_GaloisRep_ResidualEquiv` | 54 | 8 | **new** | `GaloisRep_Residual` |
| `Def_GaloisRep_Adic` | 207 | 21 | **new** | `GaloisRep_Residual`, `GaloisRep_ResidualEquiv`, mathlib |
| `Def_GaloisRep_DeformationRingData` | 46 | 7 | **new** | `GaloisRep_Adic`, mathlib |
| `Def_CuspForm_HeckeGaloisRepDatum` | 38 | 6 | **new** | `GaloisRep_Adic`, `Def_CuspForm_HeckeAlgebra` (ported) |
| `Def_CuspForm_HeckeLocal` | 440 | 67 | **new** | `HeckeGaloisRepDatum`, `CuspForm_IntegralStructure` (ported), 3 theorems |
| **new total** | **~1,290** | **~189** | | |

Already ported and to be reused (do **not** re-derive): `Def_ModularForm_HeckeOperator`,
`Def_ModularForm_HeckeOperatorForms`, `Def_CuspForm_HeckeAlgebra`,
`Def_CuspForm_IntegralStructure`, and the eigenform half of
`Def_FLTPrelim_Modularity` (`CuspForm.IsNormalizedEigenform`, `ModularFormClass.qCoeff`).

**The three theorems pulled in** by `Def_CuspForm_HeckeLocal` (statements verbatim
from their `Theorems/` wrappers; all mathlib-only proofs):

```lean
theorem IsAdicComplete.of_module_finite {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : IsAdicComplete I M

theorem IsLocalRing.isAdicComplete_of_module_finite {𝒪 : Type u} {T : Type v} [CommRing 𝒪]
    [IsNoetherianRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [IsLocalRing T]
    [IsLocalHom (algebraMap 𝒪 T)] : IsAdicComplete (IsLocalRing.maximalIdeal T) T

theorem Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] (A : Type) [CommRing A]
    [Algebra 𝒪 A] [Module.Finite 𝒪 A] :
    Finite (MaximalSpectrum A) ∧
    Function.Bijective (RingHom.pi fun I : MaximalSpectrum A =>
      algebraMap A (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A, Module.Finite 𝒪 (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A,
      IsAdicComplete (IsLocalRing.maximalIdeal (Localization.AtPrime I.asIdeal))
        (Localization.AtPrime I.asIdeal))
```

## 1. Port layout and order

Follow the playbook's module rule (§7.1: a module is a mathematical role) and
directory rule (§8). Proposed layout — the executor may reorganize within a
theory, but keep the pin's declaration names and the statement spelling.

| pin module | port module |
|---|---|
| `Def_Algebra_PatchingDatum` | `FLTForHuman/Patching/Defs/PatchingDatum.lean` |
| `Def_FLTPrelim_Modularity` (Weierstrass block) | `FLTForHuman/WeierstrassCurve/Defs/Modularity.lean` |
| `Def_FLTPrelim_GaloisRep` | `FLTForHuman/GaloisRep/Defs/GaloisAction.lean` |
| `Def_FLTPrelim_FreyPackage` | `FLTForHuman/WeierstrassCurve/Defs/FreyPackage.lean` |
| `Def_FLTPrelim_Ramification` | `FLTForHuman/GaloisRep/Defs/Ramification.lean` |
| `Def_EllipticCurve_FrobeniusTrace` | `FLTForHuman/GaloisRep/Defs/FrobeniusTrace.lean` |
| `Def_GaloisRep_Residual` | `FLTForHuman/GaloisRep/Defs/Residual.lean` |
| `Def_GaloisRep_ResidualEquiv` | `FLTForHuman/GaloisRep/Defs/ResidualEquiv.lean` |
| `Def_GaloisRep_Adic` | `FLTForHuman/GaloisRep/Defs/Adic.lean` |
| `Def_GaloisRep_DeformationRingData` | `FLTForHuman/GaloisRep/Defs/DeformationRingData.lean` |
| the three algebra theorems | `FLTForHuman/Algebra/FiniteAlgebraComplete.lean` |
| `Def_CuspForm_HeckeGaloisRepDatum` | `FLTForHuman/HeckeGalois/Defs/HeckeGaloisRepDatum.lean` |
| `Def_CuspForm_HeckeLocal` | `FLTForHuman/HeckeGalois/Defs/HeckeLocal.lean` |

The lakefile globs `.submodules`, so new directories need no build-file change
(playbook §8). Keep every import specific; do not add `import Mathlib` anywhere.

### SET order (build after every module, playbook §5.5)

- **SET A — the independent leaves.**
  1. `Patching/Defs/PatchingDatum.lean` (mathlib only; 44 lines).
  2. `WeierstrassCurve/Defs/Modularity.lean` — the `WeierstrassCurve` block of
     `Def_FLTPrelim_Modularity`: `card`, `traceOfFrobenius`, `reductionMod`,
     `apOfModel`, `IsGoodPrimeFor`, `IsSemistableModel`, `IsIntegralModelOf`,
     `IsModularModelOfLevel`, `IsModularModel`, `IsModular`, and the
     `Affine.Point.instFinite`/private pairing helper. Reuse the ported
     `CuspForm.IsNormalizedEigenform`/`qCoeff`; do not re-add them.
  3. `WeierstrassCurve/Defs/FreyPackage.lean` (mathlib only; 97 lines).
- **SET B — the Galois substrate, bottom-up.**
  4. `GaloisRep/Defs/GaloisAction.lean` (mathlib only).
  5. `GaloisRep/Defs/Ramification.lean`.
  6. `GaloisRep/Defs/FrobeniusTrace.lean`.
  7. `GaloisRep/Defs/Residual.lean`.
  8. `GaloisRep/Defs/ResidualEquiv.lean`.
  9. `GaloisRep/Defs/Adic.lean` (the largest, 207 lines).
  10. `GaloisRep/Defs/DeformationRingData.lean`.
- **SET C — the algebra cluster.**
  11. `Algebra/FiniteAlgebraComplete.lean` — the three theorems of §0. Port the
      proofs from `P2M/Sol/S_*`; they are mathlib-only. Keep helper blocks
      `private` (playbook §7.1) so the checker's public-surface diff stays exact.
- **SET D — the T package.**
  12. `HeckeGalois/Defs/HeckeGaloisRepDatum.lean` (38 lines; pulls the ported
      `heckeAlgebra`).
  13. `HeckeGalois/Defs/HeckeLocal.lean` (440 lines, 67 decls; the one module
      that uses the three theorems). This is the bulk of SET D — port it in
      pieces (the lattice restriction block, the character/localisation block,
      the structure block, the trio engines, then the three instances) and build
      after each piece with `lake env lean`.
- **SET E — wiring and verification.**
  14. Checker, consumer, full build, `#print axioms`, record (§3–§4).

## 2. The FLT → mathlib table

Build this first and test the entries (playbook §3.1, §5.2). The T-side is
mathlib-adjacent: no new mathematics is needed for the substrate.

| pin object | adopt | note |
|---|---|---|
| torsion of a curve's points | `Submodule.torsionBy ℤ (W'⁄K).Point n` | already the port's interface (playbook §2) |
| `instModuleZModTorsionBy` | `Submodule.torsionBy.zmodModule` | supersedes FLT's instance (playbook §4) |
| places, inertia, decomposition | `ValuationSubring`, `A.inertiaSubgroup K`, `A.decompositionSubgroup K` | mathlib `RamificationGroup`; `LiesOverPrime`/`inertiaSubgroupIn` are FLT's thin wrappers |
| residue field | `IsLocalRing.ResidueField`, `IsLocalRing.residue` | mathlib |
| power series | `MvPowerSeries (Fin r) 𝒪`, `MvPowerSeries.X` | mathlib; `PatchingLevel` is FLT's structure |
| localisation | `Localization`, `IsLocalization`, `IsLocalization.AtPrime` | mathlib; `heckeLocal` is FLT's localisation |
| maximal spectrum | `MaximalSpectrum`, `Localization.AtPrime` | mathlib |
| adic completeness | `IsAdicComplete` | mathlib |
| base change | `LinearMap.baseChange`, `TensorProduct` | mathlib |
| `WeierstrassCurve` arithmetic | `W.toAffine`, `W.Δ`, `W.c₄`, `W.map` | mathlib; `card`/`traceOfFrobenius`/`apOfModel` are FLT's |
| Hecke algebra, lattice, eigenform | the port's `CuspForm.heckeAlgebra`, `heckeTLin`/`heckeULin`, `intLattice`, `HasIntegralStructure`, `IsNormalizedEigenform` | reuse, do not re-derive |

FLT's structures have **no mathlib analogue** (`ResidualGaloisRep`,
`GaloisRepAdic`, `Equiv`/`IsEquiv`, `DeformationRingData`,
`HeckeGaloisRepDatum`, `PatchingLevel`/`PatchingDatum`): port them verbatim,
including field order, because the checker compares a structure as "header plus
the ordered field names".

## 3. Wiring

- **`spec/check_flt_statements.py`.** Append to `SOURCES` the pin files:
  `Definitions/Def_FLTPrelim_GaloisRep.lean`,
  `Definitions/Def_FLTPrelim_Ramification.lean`,
  `Definitions/Def_EllipticCurve_FrobeniusTrace.lean`,
  `Definitions/Def_GaloisRep_Residual.lean`,
  `Definitions/Def_GaloisRep_ResidualEquiv.lean`,
  `Definitions/Def_GaloisRep_Adic.lean`,
  `Definitions/Def_GaloisRep_DeformationRingData.lean`,
  `Definitions/Def_FLTPrelim_FreyPackage.lean`,
  `Definitions/Def_CuspForm_HeckeGaloisRepDatum.lean`,
  `Definitions/Def_CuspForm_HeckeLocal.lean`,
  `Definitions/Def_Algebra_PatchingDatum.lean`,
  and the three wrappers
  `Theorems/Thm_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite.lean`,
  `Theorems/Thm_IsAdicComplete_of_module_finite.lean`,
  `Theorems/Thm_IsLocalRing_isAdicComplete_of_module_finite.lean`.
  `Definitions/Def_FLTPrelim_Modularity.lean` is already listed, so the
  `WeierstrassCurve` block is checked without a new entry. Append every new port
  module to `PORT_FILES` (playbook §9: a moved declaration must be added at its
  new path or it silently stops being verified).
- **Consumer.** Add `spec/TsideConsumer.lean` importing the new modules, with
  four zones of *real* cross-module compositions (not `#check`s, and not
  `sorry`-terminated — playbook §7.2):
  - **residual:** build `WeierstrassCurve.residualGaloisRepOf` (from
    `Residual.lean`) and use `ResidualGaloisRep.IsEquiv`/`baseChangeAlong`
    (from `ResidualEquiv.lean`) on it;
  - **adic:** take a `GaloisRepAdic` and use `residual` (from `Adic.lean`)
    together with `ResidualGaloisRep.IsAbsolutelyIrreducible` (from
    `Residual.lean`);
  - **deformation:** state a `GaloisRep.DeformationRingData` and project
    `universal` at a test algebra;
  - **T package + local algebra:** instantiate `HeckeGaloisRepDatum` over
    `CuspForm.heckeLocal` and expose `charpoly_frob`; instantiate
    `Algebra.PatchingLevel`.
  Each zone must import from **two different** new modules, so an unwired module
  fails to build.

## 4. Verification gates

1. `cd lean && timeout 180 lake build` — green, no `sorry`/`admit`.
2. `python3 spec/check_flt_statements.py` — **0 mismatched, 0 missing**; the
   identical count rises by the number of new public declarations. Verify the
   checker itself by mutating one token of one new statement and confirming it is
   reported (playbook §7.4).
3. `#print axioms` on the layer's headline: the three algebra theorems, the
   `heckeLocal` instances, and `residualGaloisRepOf` — expect only `propext,
   Classical.choice, Quot.sound`.
4. `spec/TsideConsumer.lean` builds with 0 errors.
5. Append a record to `../logs/` (a new `t-side-port.md`) with the friction log
   kept *during* the port (playbook §3.10, §5.10), and update
   `../README.md`'s module table.

## 5. Known shape risks

- **`Submodule.torsionBy` takes `n : ℤ`** in this mathlib, so FLT's `n : ℕ`
  spellings need `↑n`, and `instModuleZModTorsionBy` should be dropped for
  `Submodule.torsionBy.zmodModule` (playbook §4).
- **`rw`/`simp only` do not unfold `abbrev`s** (`baseChange` is an `abbrev`);
  use `change` or `simp only [name]` (playbook §3.7).
- **The rewrite-search gap** (playbook §3.5) will bite on `LinearMap.baseChange_*`
  and `TensorProduct` lemmas; add a monomorphic helper the moment a `rw` reports
  no progress.
- **`haveI` in a `Prop` goal** trips `linter.style.haveILetI`; prefer `have` or
  delete when the instance came from `intro` (playbook §4).
- **`MaximalSpectrum`/`Localization.AtPrime` API drift** is the main unknown in
  SET C; the pin's proofs are the guide, and a `#check @name` probe in
  `Scratch.lean` is the first move on any name error (playbook §3.9).
- **Do not touch the FFG or other port modules**, and do not add or raise
  `maxHeartbeats` (the lakefile's global cap is 4,000,000).

## 6. Pointers

- [porting-playbook.md](../../porting-playbook.md) — the method; §3.11 build
  discipline, §4 drift checklist, §5 the checklist, §7 definitions layers, §9
  promotion and `Defs/`.
- [../../math/018-t-side-definitions.md](../../math/018-t-side-definitions.md) —
  the mathematics of every declaration here.
- [../../studies/r-equals-t-in-the-proof-base.md](../../studies/r-equals-t-in-the-proof-base.md)
  — the R=T route, the graph numbers, and how this layer is consumed.
- [../PORTING-Hecke.md](../PORTING-Hecke.md) §3.2, §5 — the port this one extends;
  [../logs/hecke-port.md](../logs/hecke-port.md) §T10 — the ported finiteness.
- [TOPIC-t8-eigenform-interface.md](TOPIC-t8-eigenform-interface.md),
  [TOPIC-t9-integral-lattice.md](TOPIC-t9-integral-lattice.md) — the two ported
  prerequisites, and the format this file follows.
