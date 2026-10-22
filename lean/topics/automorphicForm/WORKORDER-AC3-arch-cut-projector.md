# WORKORDER-AC3 — the archimedean type projector on the K-finite cut

**Status: landed (2026-10-22).** Both modules green and frozen, nothing outside them touched; the
measured reading is §9. The ground was frozen at dispatch: the q-expansion re-homing and
WORKORDER-RP1 landed, and this set was **pure addition** — two new modules, each with its own
mathematical subject, no existing module edited. Scoping:
[TOPIC-arch-cut-projector.md](TOPIC-arch-cut-projector.md).

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
| `AutomorphicForm/Adelic/ArchApproxIdentity/{ArchInfra,EntryBall,Instantiate}.lean` | the approximate-identity theorem family; `ArchInfra` happens to carry the compactness/second-countability lemmas we call (`Q09AIarch.isCompact_rowIsometrySubgroup₀`). **Import.** |

**Ruling.**

* **E1 — the engine**: new module `AutomorphicForm/Adelic/ArchCompactOrbit.lean`, namespace
  `AutomorphicForm.ArchCompactOrbit` — the archimedean product compact group and its right-regular
  action on functions on `AdelicGL2`, and the carrier of continuous functions with finite-dimensional
  orbit span together with its restricted representation. It states no headline, because it is the half
  two nodes share — the `BiIsotypic`/`TateSlots`/`Q09` precedent. That is a statement about the
  mathematics, not about wiring: its header carries `spec-pin:` lines naming the
  pin's `Theorems/` wrapper and `P2M/Sol/S_` file, and `spec/check_port.py` then diffs **every public
  declaration** of it against those sources.
* **E2 — the headline module**: new module `AutomorphicForm/Adelic/ArchCutProjector.lean` — the
  type-component split, the projector, and the headline public at `AutomorphicForm.` at the wrapper's
  statement. It is **not a wrapper around E1**: its subject is the K-finite archimedean cut and the type
  projector on it, mathematics E1 does not state, so it is a module in its own right (homing rule 1's
  subject test and rule 4's natural-name test agree). Same wire: `spec-pin:` lines for the pin's
  `Theorems/` wrapper and `S_` file, every public declaration diffed.
* **Visibility is a consumer question.** Public by default. Make a declaration `private` only when
  nothing outside the module uses it: check with `python3 tools/deps/shapes.py --module <file>
  --port-only`, which reports whether the declaration's statement shape occurs in another port module,
  and read the pin's own downstream files. Do **not** use `private` to keep a diff small — a `private`
  declaration is simply not diffed, so a module's wired surface is exactly its public surface and the
  expected `ok` count is its public declaration count. `spec/decl_markers.tsv` (loaded by
  `spec/decl_markers.py`) is for genuine exceptions only: a `pin:` rename the `spec-pin:` files do not
  carry, or an `own:` reason. Do not add rows speculatively.
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
| `isCompact_rowIsometrySubgroup₀`, the second-countability/Haar prelude | `AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean` (`Q09AIarch.*`) — same names, different binder skeleton | **import and adapt** |
| `Ecf` (continuous + finite-dimensional orbit span), `ρc` | **new** — the carrier and its representation are the engine's core. `SliceCentrality.contSubmodule` is the same *construction* on the archimedean group without the finiteness condition: read it, and share a generic lemma only if one falls out cheaply; do **not** restate `contSubmodule` | **new** |

Recorded negatives: do not port the pin's `solution`/`impl` staging; do not re-prove anything above; do
not touch `RepTheory/BiIsotypic.lean` or any `RightConvComm/` module — if a promotion there is truly
needed, **stop and report** (with `build_ladder.py --edit`'s price).

## 3. Name rectification (the pin's tokens are not mathematics)

Engine declarations are rectified; the headline keeps the pin's name (the checker keys on it).

**Status of this table: not applied — legibility debt, not a law (2026-10-22).** The landing keeps the
pin's spellings (`ArchIsometryProd`, `archRep`, `Ecf`, `ρc`, `ℂK`, `cutc`, `cutM`, `goodComponents`,
`CA`, `CB`, `projCA`, `QM`, `Qc`, `underSub`), for one reason only: `check_port` compares statement
*text*, so renaming a declaration rewrites every statement that mentions it and each of those becomes
`MISSING` (a `pin:` row flips it to `MISMATCH`, which is no better). That is a checker limitation, not
an argument about names — the checker can follow a rename once it applies the module's `pin:` map to
both sides before hashing (CARRY-FORWARD, "the AC3 engine carries the pin's engine tokens"), and the
renames are declared already. So the table below is the **target spelling** for the pass that does
the rename, not a closed question: `Ecf`, `ρc`, `QM`, `Qc`, `CA`, `CB`, `cutc`, `cutM`, `underSub` and
`goodComponents` cannot be found by subject, and the port should not ship them as API. E1 landed at
448 lines / 33 declarations (31 public, pin-named, `31 ok`).

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
   instantiations. It must be green and frozen before E2 is written.
2. **E2, the headline module**: the type-witness set (`Σ i, {T // IsRightEquivariant …}` and its
   finite-set existence), the arch cut inside the carrier, the isotypic-component split
   (`typeComponents`, the two sups, their `IsCompl`), the projector on the module and its transport to
   the carrier, and the headline assembled from the three properties.
3. Statements: the headline verbatim from `Theorems/Thm_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate.lean`;
   everything else in E1 and E2 keeps the pin's statement, checked by the same `spec-pin:` wire.

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
flock .lake/flt_build.lock timeout 120 python3 spec/check_port.py --force \
  FLTForHuman/AutomorphicForm/Adelic/ArchCompactOrbit.lean \
  FLTForHuman/AutomorphicForm/Adelic/ArchCutProjector.lean
# expected, per module: 0 mismatch, 0 missing, 0 own, 0 kw, and ok = that module's public declaration
# count. Both headers name two `spec-pin:` files, as `Adelic/Cusp/ArchTypeSpan.lean` does: the `Theorems/`
# wrapper, whose text the headline transcribes, and the `P2M/Sol/S_` comparable copy, which carries every
# engine statement — so no declaration-level marker is needed for a statement to be checked.
python3 spec/check_port.py --changed --strict-markers   # tree still green, no stale marker row
```

plus: both modules elaborate clean at 200k; `lake build` green with **0 warnings**; `#print axioms` on
the headline `[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`import Mathlib`/`set_option`;
`git status` shows exactly the two new files.

## 7. Stop conditions

Stop and report, do not improvise, if: a promotion or any edit to an existing module is needed (give the
declaration, host and `build_ladder.py --edit` price); a heartbeat raise looks necessary (give the
statement-only probe at 200k); the bridge `typeSubmodule_eq_typeSpan` does not apply in the shape needed
(say which side differs); the headline reads `MISMATCH`; a statement cannot be diffed under the
`spec-pin:` files as written and would need a `pin:` row in `spec/decl_markers.tsv`; or the carrier's
`FiniteDimensional` construction cannot close at 200k.

## 8. Report shape

(i) both modules: line and declaration counts, the public/private split with the
`shapes.py --module <file> --port-only` reading behind every `private` decision, and each module's public
surface; (ii) the two module checker readings, `--changed --strict-markers`, and the build's
jobs/warnings; (iii) axioms; (iv) the reuse actually taken versus §2's table, with each substitution
confirmed by `exact` (and any the table predicted that did not hold); (v) every rectified name;
(vi) deviations with sites; (vii) what belongs in CARRY-FORWARD.md; (viii) `git status`.

## 9. Landed (2026-10-22)

| module | lines | decls | public | private | checker |
|---|---:|---:|---:|---:|---|
| `AutomorphicForm/Adelic/ArchCompactOrbit.lean` (E1) | 448 | 33 | 31 | 2 | `31 ok, 0 mismatch, 0 missing, 0 own, 0 kw` |
| `AutomorphicForm/Adelic/ArchCutProjector.lean` (E2) | 825 | 50 | 48 | 2 | `48 ok, 0 mismatch, 0 missing, 0 own, 0 kw` |

Tree: `check_port --changed --strict-markers` **4112 ok, 0 mismatch, 0 missing, 12 own, 0 kw over 163
modules**, 0 stale markers (the 12 `own` are pre-existing rows; none added). `lake build` of the pair:
green, 3,884 jobs, **0 warnings**. Axioms on the headline:
`[propext, Classical.choice, Quot.sound]`. Only `set_option autoImplicit false` in either file; no
`sorry`/`admit`/`native_decide`/`import Mathlib`; `git status` adds exactly the two files.

**§2's table, after the event** — four of its rows did not hold, and the corrections matter for the two
siblings:

* `typeSubmodule_eq_typeSpan` (SliceCentrality:76) is **one codomain short**: its `e` lands in
  `GL (Fin 2) (InfiniteAdeleRing F)`, the cut lives on `AdelicGL2 (𝓞 F) F`. E2 carries a `private`
  12-line adapter at arbitrary `G`; the generic bridge belongs in `BiIsotypic` (CARRY-FORWARD).
* `mem_orbitSpan_self`, `orbitSpan_le_of_mem`, `archRep_mem_orbitSpan`, `continuous_of_mem_orbitSpan`,
  `map_orbitSpanc`, `orbitSpanc_mem_invtSubmodule` have **no** `BiIsotypic` counterpart — they are
  ported at the pin's statements, not instantiated (`apply_mem_typeSpan`/`map_mem_typeSpan` are
  `typeSpan` lemmas needing a commuting endomorphism).
* `isSemisimpleModule_ρc` needs mathlib's `isSemisimpleModule_of_isSemisimpleModule_submodule'`, not
  `BiIsotypic.isSemisimpleModule_hull`.
* mathlib's `RingTheory/SimpleModule/Isotypic.lean` states `sSupIndep_isotypicComponents` (:288) and
  `sSup_isotypicComponents` (:478) but **not** `isCompl_biSup_isotypicComponents`,
  `exists_add_eq_of_isCompl_biSup_isotypicComponents`, `exists_eq_span_singleton_of_isSimpleModule`,
  `le_biSup_isotypicComponents` — all four are ported (generic, and they diff `ok`).

**Taken as predicted**: `BiIsotypic.orbitSpan` (`orbitSpan`/`orbitSpanc` *are* it, `rfl`-checked by two
private bridges), `finiteDimensional_orbitSpan` (8 lines replacing 30),
`Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous`,
`Representation.exists_extend_forall_apply_mul_of_injective`,
`Q09AIarch.isCompact_rowIsometrySubgroup₀` (3 lines replacing 33). `BiIsotypic.isIrreducible_dual` was
**not** needed — the pin's copy is unused in this node, so it and `coann` are dropped. Neither module
imports `RightConvComm/SliceCentrality` (E1 does not need it; the bridge cannot typecheck in E2).

**§3 rectification: deferred, not dropped** — the pin's spellings ship because the wire compares
statement text, which is a checker limitation to fix (`pin:`-driven rename map, CARRY-FORWARD) rather
than a verdict on the names. Both module headers explain the current wire so that a later reader does
not "fix" a name into a `MISSING`; they are updated in the rename pass.

**Deviations**: `projCA*` use `Submodule.projectionOnto*` (`linearProjOfIsCompl` is a deprecation alias
since 2026-05-04; statements unchanged); two `_`-prefixed `have`s (`_hS'`, `_hc`) for binders the pin's
own proofs leave unused; `orbitSpan`/`orbitSpanc`/`placeOrbitSpan` written at the concrete
`Submodule.span` (a semireducible head breaks `span_induction`); term-position `letI` everywhere instead
of `haveI`, so no `set_option linter.style.haveILetI false`; the pin's four
`backward.isDefEq.respectTransparency false` sections and its `solution` staging dropped.

**Elaboration note for §3.5**: neither module aborts at 200k with proofs in place, so no module-level
floor was needed. The one probe was targeted — `projCA_apply_left`/`_right` with proofs `sorry`'d came
back green, which moved the diagnosis from the frozen types to the proof term, and the fix was
`inferInstance` for `_` in an `@`-application (playbook §6).
