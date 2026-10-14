# WORKORDER-SC3 — the determinant-norm slab fundamental domain

Port `AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc`
(node 6616): for a number field `F` and any `α β : ℝ` (no order assumed), a set
`S ⊆ {g | ideleNorm F (det g) ∈ Icc α β}` that is an `IsFundamentalDomain` for the left action of
`(globalPoints (𝓞 F) F).range` against `adelicGLHaar` restricted to the slab. It is the producer of
the `hS` argument the weighted-Petersson headline (WORKORDER-SC2) takes, and it sits on the
ready shelf at 475 silo lines with `used_by` 10 (cone) / 33 (project).

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

**The defs+ ground is already paid.** The node's two premises
(`NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc` and
`AutomorphicForm.ideleNorm_det_globalPoints`) are public — the latter was homed in
`AutomorphicForm/Adelic/IdeleNormDet.lean` in the SC2 round — and both `Def_*` imports
(`Def_NumberField_TateGlobalZeta` at tier 3, `Def_NumberField_AdelicBox` in `SOURCES`) are homed.
**No definition layer, no promotion and no hub edit is owed**: unlike SC1/SC2 there is no manager's
ground to wait for.

## 1. Scope

Port the pin `S_` file whole — 475 raw lines, 26 declaration groups, **354 net new math lines**,
0 duplicate copies, **2 trusted substitutions** (below).

The three pieces:

| piece | pin lines | note |
|---|---|---|
| the generic engine (`section Generic` / `Engine`, in `DetNormSlabFundamentalDomain`) | 26–244 | `exists_isOpen_one_mem_mul_inv_subset`, `rightTranslate`, `orbitMeets`, `fdPiece`/`fdUnion`, `exists_exact_fundamental_domain` (156, the ~90-line tile constructor), … |
| the two reuse rows | 246, 263 | already in the port; **import, do not transcribe** |
| the adelic specialisation | 342–467 | `val_globalPoints`, `globalPoints_mul_mem_slab`, `exists_subset_slab_isFundamentalDomain` (416) |
| the headline | 468–475 | state from the `Theorems/` wrapper (below) |

**Not this order:** the checker wiring, `UNWIRED-PUBLIC.md`, and any existing module.

## 2. Sources and deliverable

* statements — `https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean`
* proofs — `https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean`

Local clone at `~/proj/fermats-last-theorem`. The wrapper is the statement authority, not the `S_`
file's `solution` spelling.

**Deliverable:** one new module,

* `FLTForHuman/AutomorphicForm/Adelic/DetNormSlabFundamentalDomain.lean`

**listed** (tier 1). Namespaces, mirroring the pin: the 25 helpers live in
`AutomorphicForm.DetNormSlabFundamentalDomain` and are **`private`**; the headline is **public** at
`AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc`, stated
verbatim from the wrapper and proved by the `exists_subset_slab_isFundamentalDomain` below it.
Because the module is listed, the checker verifies the headline (and `-- pin:` is owed on it; the
private helpers may carry it for traceability but the register does not read it).

No other file is created or edited.

## 3. Transcription rules, reuse, and the hub prohibition

* Rename the pin's mangled chapter (`P2MW.S_<stem>`, and the inner `DetNormSlabFundamentalDomain`)
  by `AutomorphicForm.DetNormSlabFundamentalDomain`; keep every declaration name verbatim. Proofs are
  transcribed and adapted, never restated; **stop and report** if a statement must change.
* **Import, do not re-prove** — the 2 trusted substitutions in the port's tier-3 register, both at
  `FLTForHuman/NumberTheory/AdelicLevel/Countability.lean`:
  `NumberField.AdelicCountability.secondCountableTopology_restrictedProduct` (pin 263, 35-line body)
  and `NumberField.AdelicCountability.isCountablyGenerated_uniformity_of_valued` (pin 246, 5-line
  body). Drop the pin's local `private` copies. (`port_advise` prices the pair at ≈40 proof-body
  lines / 96 full declaration spans; `port_plan`'s 354 net already subtracts the latter.)
* The already-public premises are stated, not re-derived:
  `NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc`,
  `AutomorphicForm.ideleNorm_det_globalPoints`; the definitions `ideleNorm` (tier-3
  `TateGlobal/Defs.lean`), `globalPoints`/`AdelicGL2` (`AutomorphicForm/Adelic/Basic.lean`),
  `adelicGLHaar`/`glBorel` (`NumberTheory/AdelicHaar/GeneralLinear.lean`), `adelicBox`.
* Apply the `v4.34.0` drift checklist as it appears (`Set.mem_setOf_eq` → `Set.mem_ofPred_eq`,
  `Set.mem_iUnion`, `ite_eq_left`/`ite_eq_right`, `haveI`→`have` in Prop goals, …); drop the pin's
  `attribute [-instance]` prelude; never transcribe `set_option maxHeartbeats`.
* **Hub prohibition.** A helper stays `private` here and is reported; never promote, rename, or edit
  an existing module. If a promotion is genuinely required, **stop and report** the declaration, the
  intended host and the `build_ladder.py --edit` price.

## 4. Named risks and stop conditions

Named risks: `exists_exact_fundamental_domain` (pin 156, ≈90 lines, the generic orbit/tile
construction — `fdPiece`/`fdUnion` disjointness and the `IsFundamentalDomain` assembly),
`exists_subset_slab_isFundamentalDomain` (pin 416), and the `Pointwise`/`ENNReal` scoped notations
the pin turns on in its generic section. Diagnose at the low cap; fix the inference, never raise
`maxHeartbeats`. **Stop and report** on: a statement change; an import inversion; a required
promotion; or a premise outside the `S_` file that is not one of the homed items above.

## 5. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap
> is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and the low
> cap is what finds it. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`.
> `lake build <module>` per finished file, serialized with `flock` and bounded with `timeout`. Per
> wave, build only the wave's affected targets — **never a bare whole-tree `lake build`**. A
> whole-tree build happens once, at the session's end, only after the user agrees to it, and never on
> the agent's own initiative.

Concretely: tier-0 loop until `DetNormSlabFundamentalDomain.lean` is exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AutomorphicForm.Adelic.DetNormSlabFundamentalDomain`.
No bare `lake build`, no dependents.

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop | exit 0, **0 warnings**, no forbidden token |
| tier-1 build | green; jobs and wall/user/sys time |
| the headline | public at `AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc`, byte-equal to the `Theorems/` wrapper (raw and normalized) under the checker's own parser |
| `port_advise.py` + `port_plan.py` on the node | 26 declaration groups, 354 net new, 2 trusted substitutions, 0 suspect; the 25 helpers present once each, none invented |
| `unwired_register.py --check` | report only (do **not** rewrite it) |

No checker run, no register edit, no wiring.

## 7. Report shape

Module and line counts; public vs `private`; tier-0 and tier-1 times; the headline byte-compare; the
two imported declarations confirmed dropped locally; risks that bit; any statement change (there must
be none); any promotion stopped on; `git status` showing only the one new file.

## 8. Manager's half and results

Worker, then manager review and wire. Checker `9699 → 9700` (**delta +1**, exactly the headline),
0 mismatched / 0 missing.

| module | lines | public | private | tier-0 (wall/user/sys) | tier-1 |
|---|---:|---:|---:|---|---|
| `Adelic/DetNormSlabFundamentalDomain.lean` (listed, tier 1) | 517 | 1 | 35 (23 helpers + 12 `scoped instance`) | exit 0, 0 warnings (3.99/5.09/2.00 s) | 3,709 jobs, 4.8 s build (7.93 s wall) |

The headline was re-checked byte-equal to the `Theorems/` wrapper (raw and normalized) with the
checker's own parser. The pin's 25 helpers are present once each: 23 written `private`, the 2
substitutions imported; the pin's 12 countability instances are transcribed. `port_advise` /
`port_plan` parity: 475 raw / 26 groups / **354 net new** / 2 trusted substitutions / 0 suspect.

**Deviations and notes (recorded).** The order's drift line suggested spelling the pin's `haveI`s as
`have`; the worker kept five load-bearing `haveI`s (they feed instance search) under narrow
`set_option linter.style.haveILetI false in` suppressions, the playbook §7/§9 sanctioned pattern
rather than a weakened proof — tier-1 is warning-free. Other drift: `Set.mem_setOf_eq` →
`Set.mem_ofPred_eq`, `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right`, one
`instSecondCountableAdicCompletion` body replaced by the port's explicit
`HeightOneSpectrum.denseRange_algebraMap` proof, and the headline's
`open`/`attribute [local instance] glBorel` re-established after the prelude (as the pin's `solution`
does). The 36 `-- pin:` comments shift the checker's `namespace_events` offsets, so `raw_declarations`
reads the last declarations under a shallower namespace — the checker matches by last name, so its
verdict and the byte-compare are unaffected (the §4 caveat, no impact here).

**Manager's half.** Wiring: the wrapper and its `S_` file appended last to `SOURCES`;
`FLTForHuman/AutomorphicForm/Adelic/DetNormSlabFundamentalDomain.lean` appended last to `PORT_FILES`.
The module is listed, so no register entry; the register is current after refresh, with
`AdelicLevel/Countability.lean` importers 1 → 2 and `TateGlobal/Defs.lean` 8 → 9 (totals stay 92
modules / 2,344 public / 2,056 with a pin original). `#print axioms` on the headline:
`[propext, Classical.choice, Quot.sound]`.

**Step-6 re-read (successors).** The node has left the ready shelf; the shelf now reads 94 candidates.
The head is unchanged: `EisensteinGeneral.LocalRam.integral_twisted_smooth_eq` (864), then
`AutomorphicForm.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule` (823)
and `AlgebraicCurve.residue_norm_eq_norm_residue_of_retraction` (697).

Files changed: `FLTForHuman/AutomorphicForm/Adelic/DetNormSlabFundamentalDomain.lean` (new),
`spec/check_flt_statements.py`, `spec/UNWIRED-PUBLIC.md`.
