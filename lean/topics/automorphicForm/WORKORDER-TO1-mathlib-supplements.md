# WORKORDER-TO1 — the mathlib supplements and base algebra of the base-change chain (W1)

Wave 1 of the twisted-orbital definition program
([TOPIC-twisted-orbital-defs.md](TOPIC-twisted-orbital-defs.md) §2). These six pin modules are the
bottom of the chain that blocks the unit-factorizable trio
([WORKORDER-UF1](WORKORDER-UF1-unit-factorizable-defs.md) §10); the trio is `needed` for the
Deligne–Serre target, so the chain is a true dependency the frontier cannot see.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`. Checker baseline **9790 identical / 0 mismatched / 0 missing / 38 own**. This wave is
tier 3 and wires nothing: checker delta **0**.

## 1. Scope

Whole nodes (playbook §2.3), in the pin's import order — only `UniformRing` imports another of the
six, so the order is free otherwise:

| # | pin module | lines / decls | home (new file) |
|---|---|---:|---|
| 1 | `Def_Mathlib_Algebra_Algebra_Hom` | 141 / 18 | `FLTForHuman/Algebra/Algebra/SemialgHom.lean` |
| 2 | `Def_Mathlib_Topology_Algebra_UniformRing` | 40 / 3 | `FLTForHuman/Topology/Algebra/UniformRing.lean` |
| 3 | `Def_Mathlib_IsModuleTopology` | 511 / 39 | `FLTForHuman/Topology/Algebra/ModuleTopology.lean` |
| 4 | `Def_Mathlib_RightActionInstances` | 179 / 14 | `FLTForHuman/Algebra/RightActionInstances.lean` |
| 5 | `Def_Mathlib_RingTheory_Localization_BaseChange` | 79 / 6 | `FLTForHuman/RingTheory/Localization/BaseChange.lean` |
| 6 | `Def_NumberField_Extension` | 199 / 35 | `FLTForHuman/NumberTheory/NumberField/Extension.lean` |

**Not this wave.** `Def_DedekindDomain_IntegralClosure`, `Def_DedekindDomain_AdicValuation_InlineSpecific`
and `Def_DedekindDomain_Completion_BaseChange` (W2, and the only cap-risking wave); the
number-field/automorphic defs (W3); the `SemiLocal`/`UnitFactorizable` gate (W4); the trio (W5).

## 2. Sources and deliverable

Each module is its own pin file under
`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/<module>.lean`; the
local clone `~/proj/fermats-last-theorem` is the working copy. Six new files, one per row above,
declaring in the pin's namespaces, every declaration **public at the pin's name**, with
`-- pin: <name> (Definitions/<module>.lean:<line>)` above each (the tier-3 register reads it
there) and a header naming the subject, the pin and the substitutions of §3. No other file is
created or edited; nothing is wired.

## 3. The rule that dominates this wave: substitute, do not transcribe a backport

All six pin modules `import Mathlib` and are **backports** — they restate mathlib lemmas the pin's
`db584cd6` lacked. For **every** declaration, first check mathlib `v4.34.0` for a declaration with
the same statement:

* if mathlib has it, the port **imports mathlib** and does **not** re-declare it (report each such
  row with the mathlib name; a declaration the port drops this way is not `missing` — it is
  substituted, and the consumer imports mathlib);
* if mathlib has a *different spelling* of it (a binder variant), keep the pin's name as a
  `private`-free thin alias only if a consumer needs the pin's spelling — otherwise import;
* only what is genuinely absent is transcribed, at the pin's name and statement.

Already visible: `Algebra.TensorProduct.comm` exists in mathlib (a landed module uses it), so
`Def_Mathlib_RightActionInstances` is expected to shrink substantially. Do the same check for
`SemialgHom`, `IsTopologicalModule`, `moduleLid`, `IsExtension`/`IsMixedExtension`. **Report the
substitution table** (pin declaration → mathlib name, or "transcribed") for all six modules.

**Replace every bare `import Mathlib` with explicit imports.** No port module carries
`import Mathlib` (the single exception in the tree, `Algebra/ZModTorsion.lean`, is not a model);
find the modules each retained declaration needs, as
`FLTForHuman/Topology/Algebra/Valued/WithZeroMulInt.lean` does for its own pin supplement.

## 4. Named risks and stop conditions

`Def_Mathlib_IsModuleTopology` declares a `class IsTopologicalModule` and instance-search lemmas
over `R M`; a local `class` can collide with a mathlib name — check first, and if mathlib now
provides the class, import it. `Def_Mathlib_Algebra_Algebra_Hom` declares `structure SemialgHom`
and `class SemialgHomClass` (same check). `Def_NumberField_Extension` uses complex embeddings
(`IsExtension`, `IsMixedExtension`) — check mathlib's `NumberField`/`ComplexEmbedding` API before
transcribing.

Diagnose any declaration that exceeds the low cap as an instance-inference defect and fix it —
never raise `maxHeartbeats`. **Stop and report** if: a retained declaration needs a `set_option`
(quote it and the pin line); a mathlib substitute has a different statement than the pin's (do not
silently use it); or a module cannot compile without editing an existing one.

## 5. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the
> cap is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and
> the low cap is what finds it. Never raise `maxHeartbeats`, never add a module
> `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized with `flock`
> and bounded with `timeout`. Per wave, build only the wave's affected targets — **never a bare
> whole-tree `lake build`**. A whole-tree build happens once, at the session's end, only after the
> user agrees to it, and never on the agent's own initiative.

Concretely: tier-0 loop until each of the six modules is exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build <module>` per finished module. No bare
`lake build`, no dependent.

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on each module, in §1 order | exit 0, **0 warnings**, no forbidden token (`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/`maxHeartbeats`) |
| tier-1 build of each module | green; record jobs and wall/user/sys time |
| substitution table | one row per pin declaration of all six modules: mathlib name, or `transcribed`; every `transcribed` row present **once** at the pin's name |
| explicit imports | no bare `import Mathlib` anywhere in the six files |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite the register) |

No checker run, no register edit, no wiring.

## 7. Report shape

Per module: path, line count, public/`private` counts, tier-0 and tier-1 times, and its
substitution table; the six modules' totals; every declaration dropped as a mathlib substitute;
every retained declaration that needed an instance fix (and the fix); any `set_option` you stopped
on; `git status --porcelain` showing only the six new files.

## 8. The manager's half (not this order)

Register the six modules in `spec/UNWIRED-PUBLIC.md`; then cut **W2** (the Dedekind adic
base-change core), which is the wave that must confront the pin's `maxHeartbeats 1200000` /
`synthInstance.maxHeartbeats 400000` / `maxSynthPendingDepth 3` / `Elab.async false` and where a
genuine non-fit is a stop-and-report to the user.

## 9. Results as landed (2026-10-14)

Six new files, tier-0 exit 0 / **0 warnings** each, tier-1 green; no stop conditions.

| module | lines | public | tier-0 | tier-1 |
|---|---:|---:|---|---|
| `Algebra/Algebra/SemialgHom.lean` | 178 | 18 | 2.8 s | 1,067 jobs, 1.06 s |
| `Topology/Algebra/UniformRing.lean` | 55 | 3 | 2.1 s | 1,399 jobs, 1.20 s |
| `Topology/Algebra/ModuleTopology.lean` | 571 | 35 (+1 `protected`) | 3.5 s | 1,687 jobs, 4.26 s |
| `Algebra/RightActionInstances.lean` | 200 | 10 | 3.5 s | 1,665 jobs, 4.07 s |
| `RingTheory/Localization/BaseChange.lean` | 109 | 6 | 2.7 s | 1,440 jobs, 1.26 s |
| `NumberTheory/NumberField/Extension.lean` | 256 | 35 | 3.7 s | 3,019 jobs, 1.81 s |

**1,369 lines; 115 pin declarations → 108 transcribed (public at the pin name) + 7 substituted**
at the time of landing. Substitutions: `continuous_mul'`/`continuous_mul` →
`IsModuleTopology.continuous_mul_of_finite`, `Module.topologicalRing` →
`IsModuleTopology.isTopologicalRing`; `algebraMap_eval` →
`Algebra.TensorProduct.right_algebraMap_apply` (**later reverted — see below**), and the pin's
`Algebra.TensorProduct.comm*` trio → `commRight`/`commRight_tmul`/`commRight_symm_tmul` (the pin's
was `≃ₐ[A]`, mathlib's `comm` is only `≃ₐ[R]` — the order's §3 hint was wrong here and the worker
corrected it).

**Superseded (W2b, 2026-10-14).** The `algebraMap_eval` substitution is **reverted**: the W2b stop
at pin `:630` proved the scoped `Algebra S (B ⊗[R] S)` must be the pin's *explicit* body
(`algebraMap := includeRight.toRingHom`), under which `algebraMap_eval` is `rfl` again and
`right_algebraMap_apply` (a `rightAlgebra` lemma) is inapplicable. The manager made that one-place
hub edit to `Algebra/RightActionInstances.lean` (1 module / 731 lines / ≈11 s). So this module
now has **8 substitutions and 107 transcribed**, not 7/108. See
[WORKORDER-TO2b](WORKORDER-TO2b-completion-base-change.md) §9.

**No instance fix was needed anywhere** — nothing exceeded the 200k cap, so no `letI`/`haveI`/
`inferInstanceAs` bricking. Seven proof adaptations for v4.34.0 drift
(`Module.Finite.exists_fin'`, non-deprecated `IsOpenQuotientMap.secondCountableTopology`,
`IsTopologicalRing.isTopologicalAddGroup`, `AlgHom.domRestrict`, the new `TensorProduct.inductionOn`
eliminator, `AlgebraMap.baseChange`'s `commutes'`, one dropped `rfl`). Two module-level linter
suppressions, both house style: `linter.style.haveILetI false` (242 port modules do the same;
`Topology/Algebra/Valued/WithZeroMulInt.lean` is the precedent) and `linter.dupNamespace false`
(mathlib does the same in `TensorProduct/Maps.lean`). No heartbeat options, no bare `import Mathlib`.

Checker **9790 / 0 mismatched / 0 missing / 38 own** — unchanged, as expected (tier 3, unwired).
Register **105 → 111 modules, 3,011 → 3,118 public, 2,723 → 2,830 with a pin original**;
`--check` current. Files: the six above, no other file edited.

**Hand-off to W2.** Use the mathlib names for the 7 substituted rows; `TensorProduct.RightActions.
Algebra.TensorProduct.comm*` no longer exists. The pin's `IsTopologicalModule` (module 3) is a
*weaker* notion than mathlib's `IsModuleTopology` and coexists; module 4 imports mathlib's, not
module 3.
