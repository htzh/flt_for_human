# WORKORDER-AC3 — the archimedean type projector on the K-finite cut

**Status: ready to dispatch (2026-10-21).** No porting has been done. The ground is frozen: the
q-expansion re-homing and WORKORDER-RP1 landed, and this set is **pure addition** — one engine module,
one listed façade, no existing module edited. Scoping: [TOPIC-arch-cut-projector.md](TOPIC-arch-cut-projector.md).

## 0. The set

| node | pin `S_` lines | `needed` |
|---|---:|---:|
| `AutomorphicForm.exists_linearMap_archCutProjector_comm_rightTranslate` | 1,273 | **1** |

The statement: there is a `ℂ`-linear endomorphism `Q` of all functions `GL₂(𝔸_F) → ℂ` with (i) `Q φ = φ`
for continuous `φ ∈ archCutSubmodule F tys`, (ii) `Q φ ∈ archCutSubmodule F tys ⊓ span(right translates
of φ)` for a continuous `φ` with finite-dimensional archimedean orbit span, and (iii) `Q` commuting with
right translation by `⨆ w, (rowIsometryInclAt₀ F w).range`.

**Not this set.** `exists_linearMap_archCutProjector` (30-line `S_`, one declaration; 11 nodes / 5,034)
and `exists_rightConv_eq_of_archCutProjector` (1,131 lines; 9 / 3,732) — both unready, both separate
orders, both one node cheaper once this lands. Nothing outside `AutomorphicForm/Adelic/`.

## 1. The homing decision — settled here, not by the agent

The engine this node shares with the `rightConv` sibling (39 pin declarations, ~500 lines, 33
byte-identical between the two files) needed a decision. Four candidates were read; all four are
**imported**, none is the home:

| candidate | why not the home |
|---|---|
| `RepTheory/BiIsotypic.lean` (`BiIsotypic`, legacy engine) | it is the *generic* (`Representation k H V`) theory — `typeSpan`, `orbitSpan`, `rightRep`, `finiteDimensional_orbitSpan`, `isIrreducible_dual`, `isSemisimpleModule_*`. Homing rule 1 puts generic theory at its own subject home; adelic objects (functions on `AdelicGL2`, `rowIsometryInclAt₀`, `archCutSubmodule`) do not belong inside it. **Import and call it.** |
| `AutomorphicForm/Adelic/RightConvComm/SliceCentrality.lean` | it already carries the two things this engine needs — `contSubmodule` (the continuous-functions carrier on the archimedean group), the bridge **`typeSubmodule_eq_typeSpan`** (`IsotypicCuspSpace.typeSubmodule e σ = BiIsotypic.typeSpan (BiIsotypic.rightRep e) σ`), and `leftRep_eq`/`rightRep_eq` — but its subject is the archimedean-slice *kernel commutation* (`convKer_comm_*`, `adelicKernel_comm`), not the projector's carrier. **Import; do not append.** |
| `AutomorphicForm/Adelic/IsotypicCuspSpace.lean` (`CuspidalConstituent` definition layer) | it *is* the definition layer this engine sits above (`typeSubmodule`, `archTypeSubmoduleAt`, `ArchTypeFamily`, `archCutSubmodule`, `rowIsometryInclAt₀`). **Import.** |
| `AutomorphicForm/Adelic/ArchApproxIdentity/{ArchInfra,EntryBall,Instantiate}.lean` | the approximate-identity theorem family; `ArchInfra` happens to carry the compactness/second-countability lemmas we call (`Q09AIarch.isCompact_rowIsometrySubgroup₀`, tier 3). **Import.** |

**Ruling.**

* **Engine**: new module `AutomorphicForm/Adelic/ArchCompactOrbit.lean`, namespace
  `AutomorphicForm.ArchCompactOrbit` — the archimedean product compact group and its right-regular
  action on functions on `AdelicGL2`, and the carrier of continuous functions with finite-dimensional
  orbit span together with its restricted representation. **Tier 3, public, registered**
  (`spec/unwired_register.py`), every declaration with a `-- pin S_:<line>` provenance comment: it is an
  engine with no headline, shared by two nodes, exactly the `BiIsotypic`/`TateSlots`/`Q09` precedent.
  Its own `spec-pin:` header is not wanted — a tier-3 engine is by definition unwired — but the register
  must be current after the landing.
* **Façade**: new module `AutomorphicForm/Adelic/ArchCutProjector.lean` — the type-component split, the
  projector, and the headline public at `AutomorphicForm.` at the wrapper's statement (homing rule 4: the
  module named for the content is the user-facing API module). Engine `private` here; **`spec-pin:`
  wired**, expected `1 ok`.
* Do **not** create a second engine for the group-action half: the carrier is defined by the
  finite-dimensionality of the action's orbit span, so the two are one subject and one module.

## 2. Reuse map — call these, never restate

| pin declaration (`F4CutWords` spelling) | port home | verdict |
|---|---|---|
| `orbitSpan`, `mem_orbitSpan_self`, `orbitSpan_le_of_mem`, `continuous_of_mem_orbitSpan`, `orbitSpan_eq_span`, `orbitSpanc`, `map_orbitSpanc` | `BiIsotypic.orbitSpan` (:643), `map_mem_typeSpan` (:667) | **instantiate** at the concrete representation |
| `finiteDimensional_placeOrbitSpan_of_mem_*` | `BiIsotypic.finiteDimensional_orbitSpan` (:685), `_₂` (:708) | **instantiate** |
| `isIrreducible_dual`, `coann` (private) | `BiIsotypic.isIrreducible_dual` (:412) — already in the port | **import** |
| `isSemisimpleModule_ρc`, `isCompl_biSup_isotypicComponents`, `map_mem_of_mem_isotypicComponents`, `exists_add_eq_of_isCompl_biSup_isotypicComponents`, `exists_eq_span_singleton_of_isSimpleModule` | `BiIsotypic.isSemisimpleModule_hull` (:487) / `_asSubmodule` (:536) / `isIsotypicOfType_asSubmodule` (:547) + mathlib `RingTheory/SimpleModule/Isotypic.lean` | **import** |
| the type-submodule ↔ type-span dictionary | **`RightConvComm/SliceCentrality.lean:76` `typeSubmodule_eq_typeSpan`** and `leftRep_eq`/`rightRep_eq` (:66/:71) | **import** — this bridge is why the pin's concrete lemmas collapse to instantiations |
| `exists_stable_compl`, `exists_invt_compl` | instantiations of the two **ported** premises: `Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous` (`RepresentationTheory/CompactGroup.lean`) and `Representation.exists_extend_forall_apply_mul_of_injective` (`RepresentationTheory/SubrepresentationExtension.lean`) | **instantiate** |
| `isCompact_rowIsometrySubgroup₀`, the second-countability/Haar prelude | `AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean` (`Q09AIarch.*`, tier 3) — same names, different binder skeleton | **import and adapt** |
| `Ecf` (continuous + finite-dimensional orbit span), `ρc` | **new** — the carrier and its representation are the engine's core. `SliceCentrality.contSubmodule` is the same *construction* on the archimedean group without the finiteness condition: read it, and share a generic lemma only if one falls out cheaply; do **not** restate `contSubmodule` | **new** |

Recorded negatives: do not port the pin's `solution`/`impl` staging; do not re-prove anything above; do
not touch `RepTheory/BiIsotypic.lean` or any `RightConvComm/` module — if a promotion there is truly
needed, **stop and report** (with `build_ladder.py --edit`'s price).

## 3. Name rectification (the pin's tokens are not mathematics)

Engine declarations are rectified; the headline keeps the pin's name (the checker keys on it).

| pin token | port name |
|---|---|
| sections `F4CutWords`, `PartB`, `PartB3`…`PartB8`, `FarmE25`, `FarmE26`, `FarmE26C3`, `PartTQE` | **gone** — the port groups by subject |
| `ArchIsometryProd`, `archProdIncl` (+`_range`, `continuous_`) | `ArchRowIsometryProd`, `archRowIsometryProdIncl` |
| `archRep` | `archRightRegular` |
| `orbitSpan` / `orbitSpanc` | the engine's `orbitSpan` at the concrete representations — no new name |
| `Ecf`, `ρc` | `ContinuousFdOrbit`, `fdOrbitRep` |
| `cutc`, `cutM` | `archCutInFdOrbit`, `archCutModule` |
| `goodComponents`, `CA`, `CB`, `projCA` | `typeComponents`, `typeComponentSup`, `complementComponentSup`, `projectorOnTypeComponents` |
| `QM`, `Qc` | `moduleProjector`, `archTypeProjector` |
| `TypeWitness` (keep, descriptive), `coann`, `underSub` | `TypeWitness`, `dualCoannihilatorRep`, `underlyingSubmodule` |

## 4. Route

1. **Engine first**, in dependency order: the product group and its inclusion; `archRightRegular` as the
   right-regular representation composed with it; the orbit span (instantiated); the carrier
   `ContinuousFdOrbit` with its representation and the closed orbit spans; the two premise
   instantiations. It must be green and frozen before the façade is written.
2. **Façade**: the type-witness set (`Σ i, {T // IsRightEquivariant …}` and its finite-set existence),
   the arch cut inside the carrier, the isotypic-component split (`typeComponents`, the two sups, their
   `IsCompl`), the projector on the module and its transport to the carrier, and the headline assembled
   from the three properties.
3. Statements: the headline verbatim from `Theorems/Thm_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate.lean`;
   everything else is engine-internal.

## 5. Build discipline — read before the first compile

* Edit loop, from `lean/`, always through the lock:
  `flock .lake/flt_build.lock timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`.
  A finished file: `flock .lake/flt_build.lock timeout 300 lake build <Module>`.
* **The 200,000 cap is a diagnostic.** No `set_option maxHeartbeats`, no
  `synthInstance.maxHeartbeats`, ever, in either module.
* **Bound the module's floor before bisecting.** A copy in `lean/tmp/` with every theorem proof stubbed
  (statements, `def`s, instances verbatim) gives the floor in one run. If the floor is over the cap, no
  proof edit can reach it: the cost is in the frozen types (a section variable's type is re-elaborated
  per command), and the levers are — in order — a variable no statement uses belongs as a `haveI` inside
  the proof that needs it, then `private abbrev` aliases for private declarations, then **stop and
  report**. Never a bump, never a weakened statement.
* **Bound, do not measure**: no `time`, no durations, no second profiling run (one trace, kept, then
  work from it). Any compile that can plausibly run a minute is a background job with its own `timeout`
  and its output redirected to a log — read the log.
* Keep turns short: one probe, one edit, one bounded compile. No whole-tree build.

## 6. Gates

```bash
cd lean
flock .lake/flt_build.lock timeout 120 python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/ArchCutProjector.lean
# expected: 1 ok, 0 mismatch, 0 missing, 0 own, 0 kw
python3 spec/check_port.py --changed          # tree still green
python3 spec/unwired_register.py --check      # tier-3 register current (the engine is in it)
```

plus: both modules elaborate clean at 200k; `lake build` green with **0 warnings**; `#print axioms` on
the headline `[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`import Mathlib`/`set_option`;
`git status` shows exactly the two new files.

## 7. Stop conditions

Stop and report, do not improvise, if: a promotion or any edit to an existing module is needed (give the
declaration, host and `build_ladder.py --edit` price); a heartbeat raise looks necessary (give the
statement-only probe at 200k); the bridge `typeSubmodule_eq_typeSpan` does not apply in the shape needed
(say which side differs); the headline reads `MISMATCH`; the engine turns out to want a `pin:` row in
`spec/decl_markers.tsv`; or the carrier's `FiniteDimensional` construction cannot close at 200k.

## 8. Report shape

(i) both modules: line and declaration counts, engine tier-3 registration line, the engine's
public surface; (ii) the three checker readings and the build's jobs/warnings; (iii) axioms; (iv) the
reuse actually taken versus §2's table, with each substitution confirmed by `exact` (and any the table
predicted that did not hold); (v) every rectified name; (vi) deviations with sites; (vii) what belongs in
CARRY-FORWARD.md; (viii) `git status`.
