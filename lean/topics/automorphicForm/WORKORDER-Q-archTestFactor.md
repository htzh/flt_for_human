# WORKORDER-Q — the archimedean approximate identity: gate + five dispatches

**Status (2026-10-13): order written; D0 ready to run.** One dispatch = one
subagent = one or two natural modules. Dispatches run **in series, one at a time**;
the manager reviews the tree between them and re-issues the next dispatch against
the tree that then exists.

**Audience.** A fresh subagent with no memory of the reconnaissance. Read §3 twice:
§3 is the protocol and §4 is the recipe you execute. The method is
[porting-playbook.md](../../porting-playbook.md) §2.3–§2.6, §3.1–§3.5, §4. Companions:
[TOPIC-archTestFactor-family.md](TOPIC-archTestFactor-family.md) (the measurement,
the layer map, the homes), [spec/UNWIRED-PUBLIC.md](../../spec/UNWIRED-PUBLIC.md),
[CARRY-FORWARD.md](../../CARRY-FORWARD.md).

**Pin.** `anthropics/fermats-last-theorem` at `aa2d8b3`; the port's mathlib is
`v4.34.0`. The silo is
`P2M/Sol/S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean`
(3,154 lines; `solution` at :3142). Raw URLs stay correct for fetching; the
[wrapper](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean#L9)
carries the statement the checker diffs.

## 1. Scope

Port the silo as **one set**: the archimedean-Haar definition gate it cannot be
stated without, then the proof split by mathematical role into an adèlic
infrastructure module, a ball/bump module, two generic representation/convolution
modules, and a thin façade carrying the headline at the wrapper's name.

Measured: 3,154 raw lines, 193 declaration groups, 39 duplicate copies, 18
boilerplate, **3,077 net new math lines**; the headline closure is 154 private
helpers ≈ 2,778 lines. The five consumer silos (823 / 854 / 3,038 / 971 lines) are
**not this set**: the family measures 7,315 net new, but this silo shares with the
other four only ≈43 lines / 2 new declarations, so the cut is the silo alone.

**Not this set:** the four consumer headlines
(`exists_isUnitFactorizableAboveOfType_*`, `exists_finTestFactor_…`,
`exists_isIrreducibleGLRep_…`); the finite-place twisted-orbital subject of
`Def_AutomorphicForm_TwistedOrbital` and its 13 import-only `Definitions/` modules;
any edit to an existing Lean module other than the single `TestFnNearIdentity`
re-pointing of §5; the pin's `P2M.Util` / `p2m_*` scaffolding; any file-wide
`set_option`.

## 2. What is already in the port (import it; never re-derive)

* `FLTForHuman/AutomorphicForm/Adelic/IsotypicCuspSpace.lean` — `ArchTypeFamily`,
  `ArchRepAt`, `archCutSubmodule`, `archFactorCutSubmodule`, `IsArchFactorBiFinite`,
  `typeSubmodule`, `IsRightEquivariant`, `archRowIsometryInclAt₀`,
  `rowIsometryInclAt₀`.
* `FLTForHuman/AutomorphicForm/Adelic/FactorizableTestFn.lean` — `archEntries`,
  `IsArchTestFactor`.
* `FLTForHuman/AutomorphicForm/Adelic/ArchType.lean` — `adelicArchGLIncl`,
  `adelicArchGLInclAt`.
* `FLTForHuman/AutomorphicForm/Adelic/TestFnNearIdentity.lean` —
  `continuous_adelicArchGLIncl` (public; the silo's substitute for its own copy).
  Its `continuous_archEntries` is **`private`**: either promote it or re-derive the
  seven-line proof locally (§5, §8).
* `FLTForHuman/AutomorphicForm/Adelic/RightConvComm/Frame.lean` — the
  `SecondCountableAdelic` block (`private scoped instance`s; the instances are
  found by search, the names are not importable) and `adelicFrame`.
* `FLTForHuman/AutomorphicForm/Adelic/RightConvComm/MeasureAssembly.lean` —
  `archBorel` (`@[reducible] def … := borel _` on
  `GL (Fin 2) (InfiniteAdeleRing F)`), statement-identical to the pin's
  `glBorelOf`.
* `FLTForHuman/NumberTheory/AdelicHaar/{Adele,GeneralLinear}.lean` — the public
  adèlic topology and `glBorel`/`adelicGLHaar` on `GL n (AdeleRing R K)`.
* `FLTForHuman/AutomorphicForm/Adelic/CarrierPins.lean`, `Adelic/*` — the
  automorphic vocabulary the assembly names.

`port_advise` reports **0 name clashes** for the slice. If a helper's statement is
one of the landed ones, delete the local copy and quote the port module in the
report.

## 3. The protocol

### 3.1 Natural module homes, natural names

* D0 lands `FLTForHuman/NumberTheory/AdelicHaar/Archimedean.lean`: `glBorelOf`,
  `borelSpace_glBorelOf`, `archHaarK`, and the port-own instance stack of §6 of the
  topic. `glBorelOf` is a `@[reducible] def`, **not** a registered
  `MeasurableSpace` instance — do not create a diamond with mathlib's Borel
  instance. Reuse `MeasureAssembly.archBorel` as the single `borel _` spelling.
* The proof lives under `FLTForHuman/AutomorphicForm/Adelic/ArchApproxIdentity/`
  and `FLTForHuman/RepTheory/`, at the namespaces the declarations force. Strip the
  pin's `P2MW.S_…` chapter prefix; keep every mathematical sub-namespace. Do **not**
  flatten two sub-namespaces with the same tail (`Q09AIarchC.Q09` vs
  `Q09AIarch.Q09`) — they carry different declarations.
* **Home by mathematics, not by pin file.** One module per role; file size is not
  what makes a build slow (§3.4).
* Do not transcribe a `p2m_open` / `p2m_reactivate` line, and do not transcribe the
  wrappers' `attribute [-simp]` / `[-instance]` preludes. If a `simp` relies on
  one, write the explicit rewrite instead.

### 3.2 Provenance comments

Every transcribed declaration carries, immediately above it (above any `@[...]`):

```lean
-- pin: archHaarK (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:401)
```

Both name and `file:line` are required: `tools/deps/unwired_register.py` reads the
comment for its `pin original` column. A missing comment shows as `—` — treat that
as a defect. For a declaration with no pin counterpart (a port-only adapter, an
anonymous instance) write a descriptive name and `-- pin: <descriptive> (<file>:<line>)`.

### 3.3 Statements verbatim modulo the name; proofs adapted

* A **statement** is the pin's, character for character after the checker's
  normalisation; a documented `v4.34.0` drift is the only permitted difference.
* A **proof** is adapted freely. If a proof needs a *statement* to change, stop and
  report (§8).
* Keep each declaration's own binder shape: section variables vs explicit binders
  is part of the statement.

### 3.4 Build-time discipline: solve instance inference, never raise the limit

**`maxHeartbeats` is not raised — not file-wide, not per declaration.** A slow
declaration is a defect in instance inference, and raising the cap hides it:

1. compile with a low cap and a wall-clock timeout:
   `timeout 120 lake env lean -DmaxHeartbeats=200000 -DautoImplicit=false <file>`;
   the first declaration to exceed the cap is the culprit;
2. diagnose it with `set_option diagnostics true` / `set_option trace.Meta.synthInstance true`
   on that declaration, temporarily, in a scratch copy — do not commit it;
3. fix the inference: supply the instance explicitly (`letI h : … := …`), use
   `inferInstanceAs (T)` with the elaborated type, apply with `@`, avoid a `def`
   that blocks unification, or expose the instance the search cannot see through a
   coercion; then re-run at the low cap — all declarations must fit;
4. report the declaration and the fix.

`InfiniteAdeleRing` is a `def`, so instance search must not be left to unfold it.
If the whole file compiles at the port's global cap but not at a low cap, that is a
finding, not a licence: report the declaration and the trace.

### 3.5 What not to do

* Do not add a second copy of a declaration to make a proof easier.
* Do not add `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` anywhere.
* A **per-declaration** linter suppression with a one-line justification is allowed
  where the pin's verbatim statement or a load-bearing `letI`/`haveI` triggers a
  style linter (`set_option linter.style.haveILetI false in`,
  `set_option linter.overlappingInstances false in`). Never a heartbeat override.
* Do not touch the definition-layer modules of §2, the consumer silos, the other
  `S_` files, or the checker — except the D0 wiring and the final façade.
* Do not reorder across dependencies: the pin's declaration order is the spine, and
  every module must compile when appended after its predecessors.

## 4. The dispatch recipe (execute this)

1. **Extract the pin text.** For the pin range, list each declaration whose *start*
   line lies in it with its full source text. Read the whole declaration; the span
   is the declaration's, not the line's. (`tools/deps/extract_wave.py <lo> <hi>`
   and the extraction snippet in the topic §10.)
2. **Classify** each declaration against §2: substitute (import), promote (a
   pin-`private` helper a public statement mentions), re-derive locally (a pin
   `private` helper with no public face), or new.
3. **Write the module(s)** at the natural names, one `-- pin:` comment each,
   statements verbatim, proofs adapted. Import the previous dispatch's module.
4. **Tier-0 loop.** `timeout 120 lake env lean -DmaxHeartbeats=200000 -DautoImplicit=false <file>`
   until exit 0 with **0 warnings**. Every failure is fixed by editing the proof or
   the instance argument, never by raising the cap.
5. **Tier-1.** `flock .lake/flt_build.lock timeout 300 lake build <module>` per
   module. Never `lake build` with no argument.
6. **Regenerate the register.** `python3 tools/deps/unwired_register.py`; the new
   module's rows must show a `pin original`, not `—`.
7. **Report** per §9 and **stop**. The next dispatch is a separate subagent against
   the tree you leave behind.

## 5. The dispatch table

| dispatch | modules | pin range | ≈ lines |
|---|---|---|---:|
| **D0** | `NumberTheory/AdelicHaar/Archimedean.lean` (new) | `TwistedOrbital.lean:57–59,401–410` | 90 |
| **Q1** | `AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean` | 9–920 | 700 |
| **Q2** | `AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean` | 520–874 | 450 |
| **Q3** | `RepTheory/TypeReproducer.lean` | 926–2131 | 1,150 |
| **Q4** | `RepTheory/ConvolutionLimit.lean` | 2216–2856 | 700 |
| **Q5** | `AutomorphicForm/Adelic/ArchApproxIdentity.lean` (façade) | 2859–3153 | 300 |

**D0 — the definition gate.** Transcribe `glBorelOf` (`TwistedOrbital.lean:57`),
`borelSpace_glBorelOf` (`:59`) and `archHaarK` (`:401–410`) at their pin names,
plus the port-own public instance stack the `S_` file needs (topic §6): second
countability of `𝔸_{L,∞}`, its matrix ring, `GL₂`, the place completions and
`∏_w rowIsometrySubgroup₀`; `T2Space` / `LocallyCompactSpace` on the matrix ring
and `GL₂`; and the `BorelSpace` fact for `glBorelOf`. Reuse `MeasureAssembly.archBorel`.
`archHaarK` is `Measure.haar` with `letI`/`haveI` supplying `glBorelOf` and
`borelSpace_glBorelOf` explicitly. The module is **tier 3** until Q5 wires the
façade; if the `continuous_archEntries` promotion is taken, it is a one-line change
in `TestFnNearIdentity.lean`, priced with `build_ladder.py --edit` first, built as
one wave, then frozen.

**Q1 — adèlic infrastructure.** `isHaarMeasure_archHaarK`, the `Kw`/`Kprod` product
Haar (`KprodTop`, `muK`, its probability/left/right-invariance instances and
integral lemmas), `inclArch`/`inclAdelic` and their continuity, the Haar scaling
(`exists_isCompact_preimage_mul_inclArch_eq`, `haarScalarFactor_map_mul_inclArch`,
`integral_archHaarK_mul_inclArch`), and the row-isometry compactness (`rowIsoSet`,
`isCompact_rowIsometrySubgroup₀`, `archRowIsometryInclAt₀` injectivity). Import
the D0 module and §2's modules; re-derive only what they lack.

**Q2 — balls and bump.** `matrixEntries`, `entryBall`, `detLocus`, `toGL`,
`exists_bump`, `exists_approxIdentity`, `tendsto_integral_mul_approxIdentity`, and
the entry-ball comparison lemmas. May be merged into Q1 if the dependency is
shallow.

**Q3 — the type reproducer (generic).** `piRep`, `coeffFun`/`dualCoeffFun`/
`transRep`, `rt`/`spanTranslates`/`exists_finiteDimensional_stable`, `piE`/`Pm`/
`Mint`/`Hm`/`Dm`, `exists_reproducer`, `Pm_entry_mem_iSup`. Mentions neither the
adèles nor `GL₂` — declare over the abstract compact group the pin uses.

**Q4 — the convolution limit (generic).** `contSubmodule`, `dconvWith`,
`convOpR`/`convOpL`, the type-membership lemmas, support,
`tendsto_integral_mul_dconvWith`, `contDiffNat_parametricIntegral_postcompCLM`,
`contDiff_parametricIntegral_mul`.

**Q5 — the façade.** `Ent`, `twoSided`, `rtStabilizer`, `exists_contDiff_dconvWith`,
`main`, and the headline at the wrapper's name. This is the **only** listed
dispatch: add the façade to `PORT_FILES` and the wrapper plus the `S_` file to
`SOURCES` (both last), run the checker, and reconcile the `identical` delta against
the one headline. A one-token mutation on the headline must move exactly one
`mismatched`, then be reverted.

The headline, verbatim (binders, order and spellings are the checker's contract):

```lean
theorem AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule
    (L : Type) [Field L] [NumberField L] (tys : ArchTypeFamily L)
    (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f) (harch : f ∈ archCutSubmodule L tys) :
    ∃ fa : ℕ → (GL (Fin 2) (InfiniteAdeleRing L) → ℂ),
      (∀ n, IsArchTestFactor L (fa n) ∧ IsArchFactorBiFinite L tys (fa n)) ∧
      ∀ g, Filter.Tendsto
        (fun n => letI := glBorelOf (InfiniteAdeleRing L)
          ∫ y, f (g * adelicArchGLIncl L y) * fa n y ∂(archHaarK L))
        Filter.atTop (nhds (f g))
```

The `letI := glBorelOf …` inside the integral is part of the statement; keep it.

## 6. Build discipline

* edit loop: `timeout 120 lake env lean -DmaxHeartbeats=200000 -DautoImplicit=false <file>`;
* finished module: `flock .lake/flt_build.lock timeout 300 lake build <module>`;
* **no bare whole-tree `lake build`**; one `lake build <module>` per module,
  serialized;
* never raise the heartbeat cap, never add `set_option maxHeartbeats`;
* new files only; the one permitted existing-module edit is the D0
  `TestFnNearIdentity` promotion, and if it is taken, build **only** that module.

## 7. Verification (per dispatch)

* tier-0 `lake env lean` at the low cap: exit 0 and **0 warnings** — including no
  heartbeat override in the diff;
* tier-1 `flock … lake build <module>` green;
* `python3 tools/deps/unwired_register.py` regenerates cleanly and the new rows
  carry a `pin original`;
* `git status` shows only the dispatch's modules (plus the regenerated register);
* a `grep` sweep of the new files: no `sorry`/`admit`/`axiom`/`native_decide`, no
  bare `import Mathlib`, no `set_option maxHeartbeats`.

Final dispatch only (Q5):

* the façade in `PORT_FILES`; the wrapper and the `S_` file in `SOURCES`, appended
  last;
* `timeout 300 python3 spec/check_flt_statements.py` — 0 mismatched / 0 missing,
  and the `identical` delta equal to the one headline;
* a one-token mutation on the headline moves exactly one `mismatched`, then revert;
* `#print axioms` on the headline is `[propext, Classical.choice, Quot.sound]`;
* a `spec/AutomorphicFormConsumer.lean` zone exercising the headline at a concrete
  `L`/`tys`, plus one zone per earlier dispatch.

## 8. Stop and report

Stop and report, with the quotation and the pin line, if: a statement cannot be
matched without moving the pin's text (the `letI := glBorelOf …` spelling is the
known trap); a proof needs an unported `Definitions/` module beyond D0's three
declarations — report the `import` verbatim; a helper is genuinely needed publicly
and is `private` in a hub (**a promotion is the manager's; this includes anything
under `Definitions/`, `RepTheory/` and `AutomorphicForm/Adelic/`**); a low-cap
failure resists a clean instance fix; or a build exceeds its bound and bisecting
does not settle it. Do **not** open the consumer silos, do not edit the definition
modules, and do not reach past this silo into the Deligne–Serre gates.

## 9. Report shape

Per dispatch: the module paths and line counts; declarations transcribed and the
pin range consumed; substitutions imported, promotions, and local `private`
re-derivations with their hosts; provenance completeness (`N/N`); tier-0 result at
the low cap and tier-1 result; any instance-inference fix (declaration + what was
wrong); the register's diff; anything deferred, with the pin line; any stop
condition hit. Keep it short — the manager reads the tree.

## 10. Reproduce

```bash
cd tools/deps
python3 port_advise.py --nodes AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule --json build/arch_ident_advise.json
python3 port_plan.py --json build/arch_ident_advise.json
cd ../lean
python3 tools/deps/unwired_register.py
timeout 300 python3 spec/check_flt_statements.py
```
