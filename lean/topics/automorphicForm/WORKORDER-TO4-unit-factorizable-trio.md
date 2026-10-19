# WORKORDER-TO4 — the unit-factorizable trio (W4)

Wave 4 of the twisted-orbital program ([TOPIC-twisted-orbital-defs.md](TOPIC-twisted-orbital-defs.md)
§2). The definitional gate is **closed**: W1–W3b landed the whole base-change chain and the two
whole def nodes, so `IsSemiLocalFactorization`, `IsUnitFactorizableAbove` and
`IsUnitFactorizableAboveOfType` are on disk in `FLTForHuman/AutomorphicForm/Adelic/TwistedOrbital.lean`
(`:541`, `:553`, `:583`). This wave ports the three ready-shelf proof silos that use them — the
`AutomorphicForm` nodes whose earlier definition gate was [WORKORDER-UF1](WORKORDER-UF1-unit-factorizable-defs.md).

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`. Checker baseline **9790 identical (671 promoted, 83 renamed), 0 mismatched, 0 missing,
38 own**. This wave is tier 3 and wires nothing: checker delta **0** (the manager's façade supplies
the **+3**).

## 1. Scope — three whole nodes, one shared development

| node | pin `S_` file | silo lines |
|---|---|---:|
| `AutomorphicForm.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule` | `S_…tendsto_rightConv_of_mem_archCutSubmodule.lean` | 823 |
| `AutomorphicForm.exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule` | `S_…_finTestFactor_…` | 854 |
| `AutomorphicForm.exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule` | `S_…_principalLevel_…` | 971 |

Each is taken **whole** (playbook §2.3). `port_plan` over the trio: 2,648 raw `S_` lines / 2,572
declaration lines, 1,239 duplicate → once-cost 1,333, 52 already in the port, **1,281 net new math
lines**, 88 distinct declaration groups, 16 trusted substitutions. The shared blocks:
**582 lines / 46 declarations across all three** (`exists_forall_rightConv_eq_smul_integral` 141,
`isHaarMeasure_archHaarK` 33, `isArchFactorBiFinite_const_smul` 26, `ne_bot_of_forall_dvd_mem` 24,
`continuous_adelicFinGLIncl` 20, `isSemiLocalTestFn_indicator_semiLocalLevelSet` 15, …) and
**151 lines / 7 declarations across the base and finTestFactor files only**
(`isSemiLocalFactorization_levelIndicator` 37, `isUnitFactorizableAboveOfType_glArch_mul_levelIndicator`
37, `mem_finiteLevelOne_iff_of_integral` 30, …). `port_advise` sees 53 names in ≥2 files, ≈1,232
removable. **Write each shared name once.**

**Every file's shape is** shared prelude → a *private* `…_of_arch` engine → the public `solution`.
The base and `principalLevel` engines are identical except for the level subgroup
(`levelOne … ⊓ finiteAdelicGL2Subgroup L` vs `principalLevel … ⊓ …`) and one open-set lemma
(`isOpen_finiteLevelOne` vs `isOpen_finitePrincipalLevel`); `principalLevel ≤ levelOne`
(`NumberTheory/AdelicLevel/PrincipalLevel.lean:35`), so the principal hypothesis is strictly
*weaker* and the principal headline is a genuine generalisation, **not** an `rfl` specialisation.
The finTestFactor file has a different conclusion (it exposes `ff` and `fa`).

**Not this order.** The tier-1 façade and all checker wiring (§9); any existing-module edit; the
deferred consumers (`convOp_mem_isotypicCuspSubmodule…` 1,231, `twistedConvOp_mem_…` 2,542).

## 2. Sources and deliverable

Statements: the three pin `Theorems/` wrappers (authority for the statement). Proofs: the three
`P2M/Sol/S_` files. Under
`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/{Theorems,P2M/Sol}/…`; the local
clone `~/proj/fermats-last-theorem` is the working copy.

**Deliverable — one new tier-3 engine module**
`FLTForHuman/AutomorphicForm/Adelic/UnitFactorizableEngine.lean`, namespace
`AutomorphicForm.UnitFactorizable`:

* the shared prelude of §1 written **once**, `private` at the pin's names (the checker skips
  `private` port declarations, so the other copies are simply not written);
* the **general-`U` engine** serving the base and principal headlines, and the **finTestFactor
  engine** beside it, both `private` (they are the old `…_of_arch` engines);
* **three public kernels** at the three wrapper statements, named
  `AutomorphicForm.UnitFactorizable.Engine.<wrapper name>`, so the manager's façade can state the
  headlines and delegate;
* `-- pin: <name> (S_<stem>.lean:<line>)` above every public declaration (the tier-3 register
  reads it there); on the `private` prelude it is optional.

No other file is created or edited; the module is not wired in this order.

## 3. The cut (a P0 scout is the first step)

Before transcribing, answer with a compiling probe and the quotation:

> Do the base and `principalLevel` `…_of_arch` engines collapse to **one** engine over an abstract
> level subgroup — say `(U : Subgroup (AdelicGL2 (𝓞 L) L))` with the openness hypothesis the pin's
> two `isOpen_finite*` calls supply — with `hlev : ∀ g, ∀ k ∈ U, f (g * k) = f g` and
> `IsUnitFactorizableAboveOfType K L tys U SK`? If yes, the base and principal kernels are two
> instantiations; if no, say exactly which hypothesis fails, and transcribe the failing engine as
> its own `private` body behind the same prelude.

Also settle whether the finTestFactor engine shares that general-`U` engine or is independent
(it has its own conclusion). **No statement may change.**

## 4. Reuse — import, never re-prove

* The definition layer: `IsUnitFactorizableAboveOfType` and `IsSemiLocalFactorization`
  (`AutomorphicForm/Adelic/TwistedOrbital.lean`), `IsArchTestFactor`/`IsFinTestFactor`
  (`Adelic/FactorizableTestFn.lean`), `IsArchBiFinite`/`ArchTypeFamily`/`archCutSubmodule`
  (`Adelic/IsotypicCuspSpace.lean`), `levelOne` (`NumberTheory/AdelicLevel/Level.lean`),
  `principalLevel` (`NumberTheory/AdelicLevel/PrincipalLevel.lean`), `rightConv`
  (`Adelic/RightConvolution.lean`).
* **The archimedean input is already ported**: each `solution` discharges its `hAI` from
  `AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule`
  (`Adelic/ArchApproxIdentity.lean`) — cite it, do not re-derive it.
* `port_advise` substitutions (16 trusted): `continuous_adelicArchGLIncl`
  (`Adelic/TestFnNearIdentity.lean`), `isHaarMeasure_archHaarK` and `locallyCompactSpace_archGL`
  (`Adelic/ArchApproxIdentity/ArchInfra.lean`, tier 3), `mem_map_conj_iff`
  (`Adelic/RightConvNeZeroPrincipal.lean`). Two helpers are port-`private`
  (`continuous_of_isArchTestFactor`, `continuous_archEntries` in `Adelic/TestFnTop.lean`): keep a
  local `private` re-derivation or adapt, and report which.

## 5. Named risks and stop conditions

The largest helpers, in the order they will bite: `exists_forall_rightConv_eq_smul_integral` (141),
`isSemiLocalFactorization_levelIndicator` (37), `isUnitFactorizableAboveOfType_glArch_mul_levelIndicator`
(37), `mem_finiteLevelOne_iff_of_integral` (30), `ne_bot_of_forall_dvd_mem` (24),
`continuous_adelicFinGLIncl` (20), `isSemiLocalTestFn_indicator_semiLocalLevelSet` (15). The
`AdelicGL2`/`AdeleRing`/`glArch`/`glFin` coercion seams and the `levelOne ⊓ finiteAdelicGL2Subgroup`
spelling are where the instance work sits. Keep the low cap and diagnose.

**Escalate early (standing rule).** On first belief that a name cannot be matched, a premise is
unported, or a promotion/hub edit is needed, send the manager a SHORT message ("blocked on `<decl>`
at pin `:NNN`; likely needs `<X>`") and continue on what is independent. A promotion is the
manager's; do not work around it locally.

## 6. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the
> cap is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and
> the low cap is what finds it. Never raise `maxHeartbeats`, never add a module
> `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized with `flock` and
> bounded with `timeout`. Per wave, build only the wave's affected targets — **never a bare
> whole-tree `lake build`**. A whole-tree build happens once, at the session's end, only after the
> user agrees to it, and never on the agent's own initiative.

Forbid **budget** options (`maxHeartbeats`, `synthInstance.maxHeartbeats`, `maxSynthPendingDepth`,
`Elab.async`, `backward.isDefEq.respectTransparency`); **keep** `set_option autoImplicit false`
(the project default). Tactic `haveI`/`letI` on a `Prop` goal trips the `haveILetI` linter in
v4.34 — use `have`/`let`.

## 7. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop | exit 0, **0 warnings**, no budget option, no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib` |
| tier-1 build | green; record jobs and wall/user/sys |
| parity | all 53 shared names present **once**; the 88 pin declaration groups covered exactly; nothing invented |
| the three kernels | present, public at `AutomorphicForm.UnitFactorizable.Engine.<name>`, byte-equal to their `Theorems/` wrappers under `old_check_stmts.raw_declarations` |
| the P0 verdict | recorded with its quotation |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite) |

No checker run, no register edit, no wiring.

## 8. Report shape

Module path, lines, public/`private` counts, tier-0 and tier-1 times; the P0 verdict and quotation;
the parity counts; every reuse edge as used; every local `private` re-derivation with its host; any
statement that had to change (there must be none); any promotion you stopped on; `git status
--porcelain` showing only the one new file.

## 9. The manager's half (not this order)

The tier-1 façade `FLTForHuman/AutomorphicForm/Adelic/UnitFactorizableTheorems.lean` (namespace
`AutomorphicForm`) stating the three wrapper headlines verbatim and delegating to the three kernels;
the checker wiring (the three `Theorems/` wrappers and their three `S_` files appended last to
`SOURCES`, the façade appended last to `PORT_FILES`); the `UNWIRED-PUBLIC.md` refresh for the
tier-3 engine; the `identical` delta reconciled to **+3**; `#print axioms`; the step-6 re-read.

## 10. Results as landed (2026-10-14) — the program is complete

**Worker.** `AutomorphicForm/Adelic/UnitFactorizableEngine.lean` — 1,346 lines, **92 declarations
(3 public kernels + 89 `private`)**, namespace `AutomorphicForm.UnitFactorizable`, kernels at
`…Engine.<wrapper name>` byte-equal to their wrappers. Tier-0 exit 0 / **0 warnings**, tier-1 green
(3,911 jobs). Only `set_option autoImplicit false`; no budget options. Parity: 88 pin declaration
groups, 51 of the 55 shared names written exactly once (the other four are the three imported
substitutions plus `solution`, covered by the kernels).

**P0 verdict: the general-`U` engine exists.** One `private`
`exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_arch_general` proves the conclusion for
abstract `(U, Ufin)` from `IsOpen Ufin`, `IsCompact Ufin`, `hincl : ∀ k ∈ Ufin, adelicFinGLIncl L k ∈ U`,
`hlev`, `hAI` and a level-specific unit-factorizability `hfact`; base and principal are its two
instantiations. The one non-abstractable input is `hfact` — the semi-local bridge is tied to the
local predicate (`IsLocalLevelOne` vs `IsLocalPrincipal`, two different `semiLocalLevelSet`s), not
to the subgroup — so the pin's reused name `semiLocalLevelSet` forced 9 `private` principal
disambiguations. The finTestFactor engine is independent.

**Manager.** Façade `AutomorphicForm/Adelic/UnitFactorizableTheorems.lean` (namespace
`AutomorphicForm`, 3 headlines verbatim, delegating to the kernels); tier-0 exit 0 / 0 warnings,
tier-1 green (3,912 jobs, 2.7 s). Wiring: the three `Theorems/` wrappers + three `S_` files
appended last to `SOURCES`, the façade appended last to `PORT_FILES`. Register **118 → 119 modules,
3,412 → 3,415 public, 3,122 → 3,125 with a pin original** (the engine, tier 3).

| check | result |
|---|---|
| checker | **9790 → 9793 identical, 0 mismatched, 0 missing, 38 own (9,831 checked)** — delta **+3**, exactly the three headlines |
| `#print axioms` on all three headlines | `[propext, Classical.choice, Quot.sound]` |
| forbidden-token sweep (engine + façade) | none |

**Step-6 re-read.** The trio's base node was the only one of the three in the D-S `needed` demand
(the `finTestFactor`/`principalLevel` siblings are not in the cone), so `needed` [F terminal] falls
**1,401 → 1,400 nodes**, 531,197 → **530,374 `S_` lines** (−823, exactly that node), `F` 960 → 964,
and the ready shelf **87 → 86** candidates, its head now
`EisensteinGeneral.LocalRam.integral_twisted_smooth_eq` (864). The two downstream consumers of the
trio's gate — `convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType`
(1,231) and `twistedConvOp_mem_isotypicCuspSubmodule_…` (2,542) — are still short of the ready
shelf on their other premises, but the definitional gate no longer blocks them.

**This closes [TOPIC-twisted-orbital-defs.md](TOPIC-twisted-orbital-defs.md) and the deferred entry
in [CARRY-FORWARD.md](../../CARRY-FORWARD.md).** Across W1–W4 the program landed 6,565 lines of new
module surface with **no** elaborator budget transcribed: the pin's `maxHeartbeats 1200000` /
`synthInstance.maxHeartbeats 400000` / `maxSynthPendingDepth 3` / `Elab.async false`,
`tensorPiAlgHom_bijective`'s 800k, and `backward.isDefEq.respectTransparency false` are all gone,
replaced by restructuring under the 200k cap, with one priced hub edit (≈11 s).
