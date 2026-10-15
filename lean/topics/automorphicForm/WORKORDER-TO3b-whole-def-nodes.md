# WORKORDER-TO3b — the two whole def nodes: `LocalOrbitalBase` and `TwistedOrbital` (W3b)

Wave 3b of the twisted-orbital definition program
([TOPIC-twisted-orbital-defs.md](TOPIC-twisted-orbital-defs.md) §2). W1, W2 and W3a are landed
(register 116 modules / 3,274 public; checker unchanged at **9790 / 0 / 0 / 38 own** — every wave
so far is tier 3). This wave lands the two whole def nodes, including the
`SemiLocal`/`AboveTier`/`AboveTierRefined` definitions the trio needs, so that W4 can state and
prove the trio directly against them.

Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Tier 3, wires nothing:
checker delta **0**.

## 1. Scope (whole nodes, pin import order)

| # | pin module | lines / decls | home | namespace |
|---|---|---:|---|---|
| 1 | `Def_AutomorphicForm_LocalOrbitalBase` | 434 / 62 | `FLTForHuman/AutomorphicForm/Adelic/LocalOrbitalBase.lean` | `AutomorphicForm` |
| 2 | `Def_AutomorphicForm_UnitFactorizableOfType` | 78 / 9 | `FLTForHuman/AutomorphicForm/Adelic/UnitFactorizableOfType.lean` | `AutomorphicForm` |
| 3 | `Def_AutomorphicForm_TwistedOrbital` | 575 / 83 | `FLTForHuman/AutomorphicForm/Adelic/TwistedOrbital.lean` | `AutomorphicForm` |

2 imports 1 (and the landed `Adelic/IsotypicCuspSpace.lean`); 3 imports 2, the landed
`RingTheory/DedekindDomain/CompletionBaseChange.lean` (W2b),
`AutomorphicForm/Adelic/SigmaCentralizer.lean` and `NumberTheory/M4aHerbrand/ArchSemilocal.lean`
(W3a). The pin's bare `import Mathlib` must be replaced by explicit imports.

**Fold, do not split: `Adelic/IntegralUnits.lean` is absorbed and deleted.** That module (UF1's
M1, 168 lines, 13 declarations) is the `IntegralUnits`/`IsBiInvariantUnder` block of pin node 1.
Home node 1 **whole** — all 62 declarations in `LocalOrbitalBase.lean` at the pin's names — and
**delete `FLTForHuman/AutomorphicForm/Adelic/IntegralUnits.lean`**. The declarations keep their
names, so the register row simply moves; there is no split node and no orphan module.

**Already landed, import and do not re-declare** (from `Adelic/ArchHaar.lean`, itself a partial of
pin node 3): `glBorelOf` (`TwistedOrbital:57`), `borelSpace_glBorelOf` (`:59`), `archHaarK`
(`:401`). The same applies to `FactorizableTestFn`'s `IsArchTestFactor`/`IsFinTestFactor` and
`IsotypicCuspSpace`'s `IsArchBiFinite`/`ArchTypeFamily`, both ported.

**Not this wave.** W4 (the trio's proof).

## 2. Sources and deliverable

Each is its own pin file under
`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/<module>.lean`; the
local clone `~/proj/fermats-last-theorem` is the working copy. Two new modules (rows 2, 3) and one
new module that folds an existing one (row 1), every declaration **public at the pin's name** with
`-- pin: <name> (Definitions/<module>.lean:<line>)` and a header naming the subject, the pin, the
fold and the substitution table. After this wave the only files are the three, and
`IntegralUnits.lean` is gone.

## 3. Substitute first, then transcribe

For **every** declaration check mathlib `v4.34.0` before transcribing; import a same-statement
mathlib declaration instead of re-declaring; transcribe only what is genuinely absent, at the pin's
name. Node 3's `SemiLocal` section is the one W2b and the trio share: `semiLocalIntegers` names
`HeightOneSpectrum.tensorAdicCompletionIntegersTo` and `semiLocalEval` names
`HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv`, both landed in
`RingTheory/DedekindDomain/CompletionBaseChange.lean` — import them, do not re-derive. **Report the
substitution table** for all three modules, and record which of node 3's declarations came from
`ArchHaar.lean`.

## 4. Named risks and stop conditions

Node 1's orbital-integral block (`IsOrbitalIntegralOn`, `IsTwistedOrbitalIntegralOn`,
`AreMatchingOn`, `Coupled`, `twistedCentralizer`) and node 3's `Twist`/`Untwisted`/`Twisted`/
`FinitePlaces`/`Archimedean`/`BelowTier` sections are the parts no earlier wave reached; node 3's
`SemiLocal`/`AboveTier`/`AboveTierRefined` are the ones W2b's definitions feed. Keep the low cap.

**Method when a declaration will not fit:** keep the 200k cap and iterate fast to find the actual
missing instance — isolate it in a scratch copy, `set_option diagnostics true in` /
`set_option trace.Meta.synthInstance true in` on it alone, read which search fails or unfolds a
coercion, supply the instance (`letI`/`haveI` with the elaborated type, `inferInstanceAs`, explicit
`@`-application) or restructure, re-run. Never raise `maxHeartbeats`, never add
`synthInstance.maxHeartbeats`/`maxSynthPendingDepth`/`Elab.async`, never `maxHeartbeats`. Tactic
`haveI`/`letI` on a `Prop` goal trip the `haveILetI` linter in v4.34 — use `have`/`let` as W3a did.

**Escalate early (standing rule).** On first belief that a declaration needs an existing-module
edit, an unported prerequisite, or an unmatched statement, send the manager a SHORT message
("blocked at pin `:NNN` on `<decl>`; likely needs `<X>`") and continue on what is independent. Do
not work around a hub defect locally, and do not narrow it for a long stretch before telling the
manager.

## 5. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the
> cap is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and
> the low cap is what finds it. Never raise `maxHeartbeats`, never add a module
> `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized with `flock` and
> bounded with `timeout`. Per wave, build only the wave's affected targets — **never a bare
> whole-tree `lake build`**. A whole-tree build happens once, at the session's end, only after the
> user agrees to it, and never on the agent's own initiative.

Build 1, then 2, then 3. Delete `IntegralUnits.lean` only once `LocalOrbitalBase.lean` is green
with its 13 declarations absorbed.

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on all three | exit 0, **0 warnings**, no forbidden token (`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/`maxHeartbeats`/`synthInstance`/`maxSynthPendingDepth`/`Elab.async`) |
| tier-1 build of each | green; record jobs and wall/user/sys |
| node 1 coverage | all 62 pin declarations present once in `LocalOrbitalBase.lean` (the 13 from `IntegralUnits.lean` included), and `IntegralUnits.lean` deleted |
| node 3 coverage | all 83 pin declarations present once; `glBorelOf`/`borelSpace_glBorelOf`/`archHaarK` imported from `ArchHaar.lean`, not re-declared |
| the trio's gate | `IsSemiLocalFactorization` (`:452`), `IsUnitFactorizableAbove` (`:463`) and `IsUnitFactorizableAboveOfType` (`:489`) present in `TwistedOrbital.lean` |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite) |

No checker run, no register edit, no wiring.

## 7. Report shape

Per module: path, lines, public/`private`, tier-0 and tier-1 times, substitution table; node-by-node
coverage counts; the fold (how many of the 13 moved, confirmation `IntegralUnits.lean` is deleted);
the three already-landed node-3 declarations imported; every instance fix with the offending
declaration and trace finding; any escalation; `git status --porcelain` showing only the three new
files (and the one deletion).

## 8. The manager's half (not this order)

Register the three modules and drop `IntegralUnits.lean` from the register; then cut **W4** — the
trio's proof port: 2,648 raw / **1,281 net new**, one general-`U` engine serving `levelOne` and
`principalLevel` (`principalLevel ≤ levelOne`), the finTestFactor variant, and three headlines.

## 9. Results as landed (2026-10-14)

Three whole nodes, 1,327 lines: `LocalOrbitalBase.lean` (540, **62 public**), `UnitFactorizableOfType.lean`
(109, 9 public), `TwistedOrbital.lean` (678, **80 transcribed + 3 imported = 83/83**). Tier-0 exit 0
/ 0 warnings each; tier-1 green (3,451 / 3,622 / 3,652 jobs). Coverage verified by name diff
against the pin: exact, no extras or duplicates. **No declaration exceeded the 200k cap and no
instance-inference defect surfaced**, so no diagnostics run and no manual instance supply was
needed; the only fixes were `haveILetI`-linter conversions (`haveI`/`letI` → `have`/`let` on Prop
goals) in 11 declarations. **No escalation.**

**The fold.** All 14 `IntegralUnits` declaration sites were absorbed into `LocalOrbitalBase.lean`
and `IntegralUnits.lean` deleted. One correction came with it: UF1 had left
`integralUnitsSet_eq_preimage` `private`, but the pin has no `private` there, so it is restored
**public** at the pin's name — the node is 62 public, not 61+1. No module imported `IntegralUnits`.

**Trio gate on disk** in `TwistedOrbital.lean`: `IsSemiLocalFactorization` (`:541`),
`IsUnitFactorizableAbove` (`:553`), `IsUnitFactorizableAboveOfType` (`:583`). Its dependencies are
imported, not re-derived: `tensorAdicCompletionIntegersTo` and `baseChangeAlgEquiv` from
`RingTheory/DedekindDomain/CompletionBaseChange.lean`, `Extension.finite` from `IntegralClosure`,
`sigmaCentralizer` from `Adelic/SigmaCentralizer.lean`, `genuineInfinitePlaceData` from
`NumberTheory/M4aHerbrand/ArchSemilocal.lean`.

**Manager follow-up (house convention).** The worker read "no `set_option` of any kind" strictly
and dropped the pin's `set_option autoImplicit false`. That option is **not** an elaborator budget
— it is the project default (the lakefile sets it package-wide, 242 port modules restate it) and
`lake env lean` does **not** inherit the lakefile's `leanOptions`, so a module without it is not
self-contained under the tier-0 loop's own flags. The manager restored it on all six W3a/W3b
modules and rebuilt them green. The rule for W4 onward: forbid **budget** options
(`maxHeartbeats`, `synthInstance.maxHeartbeats`, `maxSynthPendingDepth`, `Elab.async`,
`backward.isDefEq.respectTransparency`), expect `set_option autoImplicit false`.

Checker **9790 / 0 / 0 / 38 own** (tier 3). Register **116 → 118 modules** (three added, one
deleted), **3,274 → 3,412 public**, **2,984 → 3,122 with a pin original**; `--check` current.
Files: the three above plus the deletion; no other file edited by this wave.

**Pre-existing warning, not this wave's.** A `lake build TwistedOrbital` replay surfaces
`haveILetI`/unused-tactic warnings in the unmodified `AlgebraicCurve/Defs/PlaceCompletion.lean`
(:418, :473); they are outside this set and would show in a warning-free whole-tree build.
