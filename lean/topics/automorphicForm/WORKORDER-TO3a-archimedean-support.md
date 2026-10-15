# WORKORDER-TO3a — the number-field archimedean-support nodes (W3a)

Wave 3a of the twisted-orbital definition program
([TOPIC-twisted-orbital-defs.md](TOPIC-twisted-orbital-defs.md) §2). W1 and W2 are landed
(register 113 modules / 3,210 public; checker unchanged at **9790 / 0 / 0 / 38 own** because every
wave so far is tier 3). This wave lands the three support nodes `TwistedOrbital` imports for its
archimedean/twisted-orbital sections; W3b then lands the two whole def nodes.

Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Tier 3, wires nothing:
checker delta **0**.

## 1. Scope (whole nodes, pin import order)

| # | pin module | lines / decls | home (new) | namespace |
|---|---|---:|---|---|
| 1 | `Def_NumberField_InfiniteAdeleRing_BaseChangeData` | 361 / 36 | `FLTForHuman/NumberTheory/NumberField/InfiniteAdeleRing/BaseChangeData.lean` | `FLT.InfiniteAdeleBaseChange`, `InfinitePlaceData` |
| 2 | `Def_M4aHerbrand_ArchSemilocal` | 284 / 23 | `FLTForHuman/NumberTheory/M4aHerbrand/ArchSemilocal.lean` | `M4aHerbrand.ArchSemilocal` |
| 3 | `Def_AutomorphicForm_SigmaCentralizer` | 62 / 6 | `FLTForHuman/AutomorphicForm/Adelic/SigmaCentralizer.lean` | `AutomorphicForm` |

1 imports the landed W1 `FLTForHuman/NumberTheory/NumberField/Extension.lean` (the pin's
`Def_NumberField_Extension`); 2 imports 1; 3 imports mathlib only. The pin's bare `import Mathlib`
must be replaced by explicit imports.

**Not this wave.** `LocalOrbitalBase`, `UnitFactorizableOfType`, `TwistedOrbital` (W3b); the trio's
proof (W4).

## 2. Sources and deliverable

Each is its own pin file under
`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/<module>.lean`; the
local clone `~/proj/fermats-last-theorem` is the working copy. Three new files, one per row,
declaring in the pin's namespaces, every declaration **public at the pin's name**, with
`-- pin: <name> (Definitions/<module>.lean:<line>)` above each and a header naming the subject, the
pin and the substitution table. No other file is created or edited; nothing is wired.

## 3. Substitute first, then transcribe

For **every** declaration check mathlib `v4.34.0` before transcribing; where mathlib has the pin's
statement, import it and do not re-declare, and where it has the underlying fact under another
name, use it. `Def_NumberField_Extension` (W1, landed) already supplies the `IsExtension`/
`IsMixedExtension`/`InfinitePlace.Extension` vocabulary this wave builds on — import it, do not
re-derive. **Report the substitution table** for all three modules. Watch for mathlib's newer
`InfiniteAdeleRing`/`NumberField/Completion` API: `NumberField/Completion/FinitePlace.lean`
(`Module.Finite Kv Lw`, the dense base-change map) and `InfiniteAdeleRing` instances may already
cover parts of module 1 (`tensorPiAlgHom`, `tensorPiAlgEquiv`, `collapsePlaces`, `InfinitePlaceData`).

## 4. Named risks and stop conditions

Module 1 is tensor/`InfiniteAdeleRing` algebra (`tensorPiAlgHom_bijective`, `tensorPiAlgEquiv`,
`collapsePlaces`, `evalAlgHom`, the `InfinitePlaceData` structure); module 2 is the archimedean
semi-local comparison (`M4aHerbrand.ArchSemilocal`); module 3 is a small centralizer predicate.
Keep the low cap.

**Method when a declaration will not fit:** keep the 200k cap and iterate fast to find the actual
missing instance — isolate the declaration in a scratch copy, run `set_option diagnostics true in` /
`set_option trace.Meta.synthInstance true in` on it alone at the low cap, read which search fails or
unfolds a coercion, supply the instance (`letI`/`haveI` with the elaborated type,
`inferInstanceAs`, explicit `@`-application) or restructure, and re-run. Never raise
`maxHeartbeats`, never add `synthInstance.maxHeartbeats`/`maxSynthPendingDepth`/`Elab.async`.

**Escalate early (standing rule).** If you believe a declaration needs an existing-module edit, an
unported prerequisite, or a statement that cannot be matched, send the manager a *short* message at
first belief ("blocked at pin `:NNN` on `<decl>`; likely needs `<X>`") and continue on whatever is
independent — do not spend a long stretch narrowing it first, and do not work around a hub defect
locally.

## 5. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the
> cap is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and
> the low cap is what finds it. Never raise `maxHeartbeats`, never add a module
> `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized with `flock` and
> bounded with `timeout`. Per wave, build only the wave's affected targets — **never a bare
> whole-tree `lake build`**. A whole-tree build happens once, at the session's end, only after the
> user agrees to it, and never on the agent's own initiative.

Build module 1, then 2, then 3 (3 is independent).

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on all three | exit 0, **0 warnings**, no forbidden token (`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/`maxHeartbeats`/`synthInstance.maxHeartbeats`/`maxSynthPendingDepth`/`Elab.async`) |
| tier-1 build of each | green; record jobs and wall/user/sys |
| substitution tables | one row per pin declaration of all three; every `transcribed` row present once at the pin's name |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite) |

No checker run, no register edit, no wiring.

## 7. Report shape

Per module: path, lines, public/`private`, tier-0 and tier-1 times, substitution table; the three
totals; every instance fix with the offending declaration and the trace finding; any early
escalation; `git status --porcelain` showing only the three new files.

## 8. The manager's half (not this order)

Register the three modules; then cut **W3b** (`LocalOrbitalBase` whole → `UnitFactorizableOfType`
→ `TwistedOrbital` whole), and only then **W4**, the trio's proof port.

## 9. Results as landed (2026-10-14)

Three new tier-3 modules, whole nodes, green: `NumberField/InfiniteAdeleRing/BaseChangeData.lean`
(326 lines, 36 public), `M4aHerbrand/ArchSemilocal.lean` (351, 22 public + 1 private `aux_ker_ne`,
private at the pin too), `Adelic/SigmaCentralizer.lean` (91, 6 public). **768 lines / 64 public /
65 pin declarations**, tier-0 exit 0 / 0 warnings each, tier-1 green (3,075 / 3,133 / 801 jobs).
No `set_option` of any kind, no escalation, nothing needing an existing-module edit.

**Two cap-risk declarations were removed rather than copied.** The pin wraps
`tensorPiAlgHom_bijective` in `backward.isDefEq.respectTransparency false` with an 800k budget; the
port restructured it as an `AlgHom` equality (`tensorPiAlgHom K L = e.toAlgHom` for an explicit
`AlgEquiv` composite) proved by `TensorProduct.inductionOn`, same statement, no option. The pin's
`maxSynthPendingDepth`-dependent `aux_ker_ne` and the `psi_surjective` / `continuous_conorm` pair
all fit the 200k cap with default instance search; the pin's `attribute [local instance] extLiesOver`
is kept as-is (an attribute is not a budget) and is what resolves the `LiesOver`-derived
`Algebra`/`Module` instances. Tactic `haveI`/`letI` whose goal is a `Prop` were rewritten to
`have`/`let` for v4.34.0's `haveILetI` linter (instance search still uses them — verified green).

**Drift recorded:** deprecated mathlib aliases the pin used → v4.34.0 names — `Pi.algHom` →
`AlgHom.pi`, `TensorProduct.induction_on` → `TensorProduct.inductionOn`,
`Completion.*_isUnramified`/`*_isRamified` → `IsUnramified.finrank_eq_one` /
`IsRamified.finrank_eq_two`, `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`. Substitutions: 0 — every pin
declaration is transcribed at its name (mathlib's `InfiniteAdeleRing.algebraMap_apply` is defeq but
differently stated, so the pin's form stays).

Checker **9790 / 0 / 0 / 38 own** (tier 3). Register **113 → 116 modules, 3,210 → 3,274 public,
2,920 → 2,984 with a pin original**. Files: the three above; no other file edited.
