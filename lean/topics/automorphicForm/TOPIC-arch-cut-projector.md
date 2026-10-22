# The archimedean type projector on the K-finite cut — scoping (2026-10-21)

The node `AutomorphicForm.exists_linearMap_archCutProjector_comm_rightTranslate`, scoped against the
frozen ground of the q-expansion re-homing and of `RepTheory/BiIsotypic.lean`. It is **ready**, one
node, and it is upstream of the two siblings that are not. This note is the decision material for its
work order; every figure is the pin's or a tool's, named where it comes from.

## 1. The node, its statement, and the family

`S_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate.lean`, 1,273 lines, 88
declarations. `frontier.py --ds --target`: one needed node / 1,273 silo lines, both premises ported
(181 lines of `F` inside the cone), `used_by` 2 cone / 3 project.

The statement, in one sentence: there is a `ℂ`-linear endomorphism `Q` of *all* functions
`GL₂(𝔸_F) → ℂ` which (i) fixes the continuous elements of `archCutSubmodule F tys`, (ii) sends a
continuous `φ` whose right translates under the archimedean compact group span a finite-dimensional
space into `archCutSubmodule F tys ⊓ span(right translates of φ)`, and (iii) commutes with right
translation by that compact subgroup.

**The family is three files, and only this one is ready.**

| node | `S_` lines | decls | `needed` |
|---|---:|---:|---:|
| `exists_linearMap_archCutProjector_comm_rightTranslate` | 1,273 | 88 | **1** |
| `exists_linearMap_archCutProjector` | 30 | 1 | 11 / 5,034 |
| `exists_rightConv_eq_of_archCutProjector` | 1,131 | 81 | 9 / 3,732 |

So **not this set**: the other two are separate orders, and both improve when this lands (11 → 10 and
9 → 8 nodes). The 30-line `projector` file is a one-declaration wrapper — its `solution` is not a
development.

## 2. What the pin file is made of, and what the tools do not see

The pin groups its 88 declarations into thirteen `section`s labelled `F4CutWords`, `PartB`, `PartB3`…
`PartB8`, `FarmE26`, `FarmE26C3`, `FarmE25`, `PartTQE` — proof-search labels, not subjects.

* **Shared prelude: 39 declarations / ≈500 lines**, 33 of them byte-identical to the same block in
  `rightConv`'s file: the archimedean product compact group and its action by right translation, the
  orbit span, the continuous-finite-orbit carrier with its restricted representation, and the two
  `Representation`-premise instantiations.
* **This node's own 48 declarations / 744 lines**: the type-witness set, the arch cut inside the
  carrier, the isotypic-component split with its `IsCompl`, the projector on the module, its
  transport to the carrier, and the three-property assembly.

`port_advise` reports **one** exact substitution and `twin_scan` reports **prelude 1/86**. Both are
blind here rather than reassuring: the prelude is mostly `def`/`abbrev`/`structure` (neither tool keys
`def`s for twins), and its *theorems* are concrete instances of a generic engine that the pin wrote in
a **different silo**, so no statement hash matches.

## 3. The engine the port already owns — `RepTheory/BiIsotypic.lean`

1,026 lines, transcribed public from `S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean`'s
`BiIsotypic` namespace. It is the generic (`Representation k H V`) form of exactly this material.

| pin declaration (generated name) | home in the port | verdict |
|---|---|---|
| `orbitSpan` (205), `mem_orbitSpan_self`, `orbitSpan_le_of_mem`, `continuous_of_mem_orbitSpan`, `orbitSpan_eq_span` | `BiIsotypic.orbitSpan` (:643, generic), through the **ported bridge** `RightConvComm/SliceCentrality.lean:76` `typeSubmodule_eq_typeSpan` (and `leftRep_eq`/`rightRep_eq` at :66/:71) | **instantiate** at `archRep`; the pin's five lemmas are the generic ones applied |
| `Ecf`'s continuity half | `RightConvComm/SliceCentrality.lean:57` `contSubmodule` — the same construction on `GL₂(A_∞)`, without the finiteness condition | **read it; share a generic lemma only if one falls out cheaply** — our carrier is on `AdelicGL2` and adds the finite-dimensional orbit condition, so it is new |
| `orbitSpanc` (336), `map_orbitSpanc`, `orbitSpanc_mem_invtSubmodule` | `BiIsotypic.orbitSpan` at the carrier's representation | **instantiate** |
| `finiteDimensional_placeOrbitSpan_of_mem_*` (476/508) | `BiIsotypic.finiteDimensional_orbitSpan` (:685), `finiteDimensional_orbitSpan₂` (:708) | **instantiate** |
| `isIrreducible_dual` (866), `coann` (851, private) | `BiIsotypic.isIrreducible_dual` (:412) — already verbatim in the port (`port_advise`'s pool duplicate); `coann` is its `dualCoannihilator` step | **import** |
| `isSemisimpleModule_ρc` (368), `isSemisimpleModule_*`, `isCompl_biSup_isotypicComponents` (430), `map_mem_of_mem_isotypicComponents` (965), `exists_add_eq_of_isCompl_biSup_isotypicComponents` (983), `exists_eq_span_singleton_of_isSimpleModule` (1004) | mathlib `RingTheory/SimpleModule/Isotypic.lean` + `BiIsotypic.isSemisimpleModule_hull` / `_asSubmodule` / `isIsotypicOfType_asSubmodule` (:487/:536/:547) | **import** |
| `exists_stable_compl`, `exists_invt_compl` (prelude) | instantiations of the two **ported** premises: `Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous` (`RepresentationTheory/CompactGroup.lean`) and `exists_extend_forall_apply_mul_of_injective` (`SubrepresentationExtension.lean`) | **instantiate** |
| `isCompact_rowIsometrySubgroup₀`, `secondCountable…`, `archHaarK` prelude | `Q09AIarch` in `AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean` (tier 3, registered) — same names, different binder skeleton | **import and adapt**, do not re-prove |

**No definition gate**: the pin's three `Definitions/` imports are all homed —
`Def_AutomorphicForm_CuspidalConstituent` (`AutomorphicForm/Adelic/Cusp/Constituent.lean`, with the
`ArchTypeFamily`/`archCutSubmodule`/`rowIsometryInclAt₀`/`typeSubmodule` vocabulary in
`Adelic/IsotypicCuspSpace.lean`), `Def_AutomorphicForm_ArchWeightChar` (`Adelic/ArchWeightChar.lean`). The third,
`Def_AutomorphicForm_AdelicMaximalCompact`, is an **inert import** in the pin: the file never names
`maximalCompact` (a `grep -c` finds the import line only), and the port's compact-vocabulary module
`Adelic/ProductionPinsCompact.lean` covers it anyway. Nothing to home, nothing to check.

**Price.** `port_plan`: 1,273 raw → **1,253 net new** (nothing statement-identical in the port) — the
*transcription ceiling*. With §3's reuse the deduped landing is **≈400–550 lines**: the carrier with
its restricted representation, the type-witness set, the component split, the projector and the
assembly. The prelude is worth homing **once** because `rightConv` carries it byte-identically.

## 4. Name rectification (the pin's tokens are not mathematics)

The pin's labels and compressed defs are artefacts of how it was written; the port states the subject.
Engine declarations are rectified; a **pin-public** statement keeps the pin's name (the checker keys on
it) and a rectified public declaration takes a `pin:` row.

| pin token | port name |
|---|---|
| sections `F4CutWords`, `PartB*`, `FarmE*`, `PartTQE` | gone — the port groups by subject |
| `ArchIsometryProd`, `archProdIncl` (+`_range`, `continuous_`) | `ArchRowIsometryProd`, `archRowIsometryProdIncl` |
| `archRep` | `archRightRegular` (the right-regular representation through the product inclusion) |
| `orbitSpan` / `orbitSpanc` | the engine's `orbitSpan` at the concrete representations (no new name) |
| `Ecf` (carrier of continuous functions with finite-dimensional orbit span), `ρc` | `ContinuousFdOrbit`, `fdOrbitRep` |
| `cutc`, `cutM` | `archCutInFdOrbit`, `archCutModule` |
| `goodComponents`, `CA`, `CB`, `projCA` | `typeComponents`, `typeComponentSup`, `complementComponentSup`, `projectorOnTypeComponents` |
| `QM`, `Qc` | `moduleProjector`, `archTypeProjector` |
| `TypeWitness` | kept (descriptive), `coann` → `dualCoannihilatorRep`, `underSub` → `underlyingSubmodule` |

## 5. The proposed set

* **E1** (tier 3 engine, registered, `-- pin:` provenance): `AutomorphicForm/Adelic/ArchCompactOrbit.lean`
  — the archimedean product compact group, `archRightRegular`, the `ContinuousFdOrbit` carrier with
  `fdOrbitRep`, the orbit-span instantiations, and the two `Representation`-premise instantiations.
  Shared by this node and by `rightConv`. **Homing settled** in the order's §1: the four candidate hosts
  (`RepTheory/BiIsotypic.lean`, `RightConvComm/SliceCentrality.lean`, `IsotypicCuspSpace.lean`,
  `ArchApproxIdentity/*`) are all *imported and called*, none is the home — the subject here is the
  archimedean compact group's action and its finite-orbit carrier, which no existing module names.
* **F1** (listed, `spec-pin:` wired): `AutomorphicForm/Adelic/ArchCutProjector.lean` — the type-witness
  set, the component split with its `IsCompl`, the projector, and the headline at the wrapper's
  statement (**+1**), engine `private`. Order: [WORKORDER-AC3-arch-cut-projector.md](WORKORDER-AC3-arch-cut-projector.md).
* No existing module is edited; all reuse is by import. A `BiIsotypic` promotion, if one turns out to be
  needed, is a stop-and-report (with `build_ladder.py --edit`'s price).

## 6. Risks

1. **The §3 table is a reading, not a tool verdict.** Each substitution must be confirmed by `exact`
   before the pin's copy is deleted; the fallback is a local `private` adapter (the FR1 pattern), never
   a re-derivation.
2. **The carrier is the one genuinely new object** (`Ecf` + `ρc`): if `BiIsotypic.subrep`/`subEquiv`
   supplies it, the engine shrinks by ~150 lines; if not, it is instance-heavy and the 200k diagnostic
   will say so — that is a probe, not a bump (`logs/build-time-issues.md` §7–§8).
3. **`rightConv` compatibility**: its copy of the prelude is byte-identical, so the engine's shapes
   should stay as generic as the pin's concrete proofs allow, or that node inherits an adapter too.
4. `Ecf`'s `FiniteDimensional`/`Continuous` carrier is where a slow declaration will hide; the engine
   and the façade must both close at the project cap (0 warnings, no `set_option`).

## 7. Successors when this lands

`exists_linearMap_archCutProjector` 11 → 10 nodes, `exists_rightConv_eq_of_archCutProjector` 9 → 8;
the demand falls one node / 1,273 raw lines, and the ready shelf loses its head.
