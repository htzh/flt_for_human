# WORKORDER-SC4 — the `IsInducedSection` pair

Two ready nodes cut together, one mathematical story (the `IsInducedSection` API of the adelic
height and its pointwise form):

* `AutomorphicForm.isInducedSection_adelicHeight_cpow` (node 7248) — the adelic height powers form
  a Borel-induced flat section: positivity of the modulus character, unitarity of the trivial
  character, and `g ↦ adelicHeight F g ^ (s + 1/2)` satisfying the induction law. 455 silo lines,
  `used_by` 7 (cone) / 41 (project).
* `AutomorphicForm.IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul`
  (node 7220) — the induced-section transformation law at global points and at unipotents.
  50 silo lines, `used_by` 2 / 10.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

**The pre-wave is landed.** `Definitions/Def_AutomorphicForm_ArchKFinite.lean` (9 declarations, the
archimedean-`K`-finiteness vocabulary the first node's proof needs, imported by 731 pin files) is
homed at `FLTForHuman/AutomorphicForm/Adelic/ArchKFinite.lean` and checker-verified (`+9`). All the
other `Def_*` imports (`InducedSection`, `EtaFamily`, `BorelSubgroup`, `WeylIntertwining` — tier 3
registered; `Def_NumberField_AdelicHeight` — in `SOURCES`) are homed, so there is **no further
manager's ground**.

## 1. Scope

| node | pin `S_` file | raw | groups | net new | visibility |
|---|---|---:|---:|---:|---|
| 1 | `S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean` | 455 | 37 | 393 | 36 public / 1 private |
| 2 | `S_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul.lean` | 50 | 1 | 36 | 1 declaration |

**429 net new lines / 38 declaration groups**, 0 duplicate copies.

Substitutions (`port_advise`): **4 trusted** — `norm_finComp_eventually_eq_one`,
`finComp_ne_zero`, `finComp_mul_finComp_inv` (all `P6B.JE2aFlat.*`) and
`hasFiniteMulSupport_norm_finComp` (`P6B.JE2aHMod.*`), all tier-3 registered and public —
**import, drop the local copies**. **1 suspect** — `placeModulus → NumberField.TateGlobal.ideleNorm`:
the pin defines `placeModulus` locally as the explicit product
`∏_w ‖x.1 w‖^{w.mult} · ∏ᶠ_v ‖x.2 v‖`, which equals `ideleNorm` only by
`distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm` and **not** definitionally. **Keep
`placeModulus` as a local `def`; do not substitute `ideleNorm`** (the §2.4 type-only-`def` false
positive).

## 2. Sources and deliverable

* wrappers (statement authority) —
  `https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean`
  and
  `https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul.lean`
* proofs — the matching `P2M/Sol/S_…lean` files.

**Deliverable:** one new **listed** module,

* `FLTForHuman/AutomorphicForm/Adelic/InducedSectionFlat.lean`

holding both nodes (they are one family; a module for the 36-line second node alone would be
disproportionate). Namespaces: node 1's declarations in `AutomorphicForm` (the headline is
`AutomorphicForm.isInducedSection_adelicHeight_cpow`); node 2's headline in
`AutomorphicForm.IsInducedSection` (`AutomorphicForm.IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul`). The pin's first node declares its 36 helpers
**public**; transcribe them at the pin's visibility, so the checker verifies the whole surface. No
other file is created or edited.

## 3. Transcription rules, reuse, and the hub prohibition

* Rename the pin's mangled chapters (`P2MW.S_<stem>`) by `AutomorphicForm` / `AutomorphicForm.IsInducedSection`;
  keep every declaration name verbatim. Proofs are transcribed and adapted, never restated; **stop
  and report** if a statement must change.
* Import, do not re-prove: the 4 trusted substitutions above; `AutomorphicForm.isArchKFinite_of_hasArchType`
  and `…isArchKFinite_const`/`_zero` (`Adelic/ArchKFinite.lean`); `IsInducedSection`
  (`Adelic/InducedSection.lean`), `etaFst`/`etaSnd` (`Adelic/EtaFamily.lean`), `IsUnitaryChar`
  (`Adelic/LsXi.lean`), `HasArchType`/`HasArchCharacterAt`/`adelicArchGLInclAt`/`archRowIsometryAt`
  (`Adelic/ArchType.lean`), `rowIsometrySubgroup` (`Adelic/WindowedSiegel/RowIsometry.lean`),
  `adelicHeight` (`NumberTheory/AdelicHeight.lean`), `adelicBorel` (`Adelic/BorelSubgroup.lean`).
* Apply the `v4.34.0` drift checklist as it appears (`Set.mem_setOf_eq` → `Set.mem_ofPred_eq`,
  `ite_eq_left`/`ite_eq_right`, `haveI`→`have` in Prop goals or a narrow local
  `set_option linter.style.haveILetI false in`, …); drop the pin's `attribute [-instance]` prelude;
  never transcribe `set_option maxHeartbeats`.
* **Hub prohibition.** A helper stays at the pin's visibility and is reported; never promote,
  rename, or edit an existing module. If a promotion is genuinely required, **stop and report** the
  declaration, intended host and `build_ladder.py --edit` price.

## 4. Named risks and stop conditions

Named risks: the adelic-height computation `adelicHeight_borel_mul` (pin 239) and the
`adelicHeight_mul_of_integral_of_rowIsometry` block (pin 289); the complex-power algebra
`ofReal_div_mul_cpow` (pin 413) and `flatOne_eq_exp`; the `IsInducedSection` assembly
`isInducedSection_flatOne` (pin 422). Diagnose at the low cap; fix the inference, never raise
`maxHeartbeats`. **Stop and report** on: a statement change; an import inversion; a required
promotion; or a premise outside the two `S_` files that is not one of the homed items above.

## 5. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap
> is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and the low
> cap is what finds it. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`.
> `lake build <module>` per finished file, serialized with `flock` and bounded with `timeout`. Per
> wave, build only the wave's affected targets — **never a bare whole-tree `lake build`**. A
> whole-tree build happens once, at the session's end, only after the user agrees to it, and never on
> the agent's own initiative.

Concretely: tier-0 loop until `InducedSectionFlat.lean` is exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AutomorphicForm.Adelic.InducedSectionFlat`.
No bare `lake build`, no dependents.

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop | exit 0, **0 warnings**, no forbidden token |
| tier-1 build | green; jobs and wall/user/sys time |
| both headlines | public, byte-equal to their `Theorems/` wrappers (raw and normalized) under the checker's own parser |
| `placeModulus` | present as a local `def`, **not** replaced by `ideleNorm` |
| `port_advise.py` + `port_plan.py` on the two nodes | 38 declaration groups, 429 net new, 4 trusted / 1 suspect; none invented |
| `unwired_register.py --check` | report only (do **not** rewrite it) |

No checker run, no register edit, no wiring.

## 7. Report shape

Module and line counts; public vs `private`; tier-0 and tier-1 times; both headline byte-compares;
the `placeModulus` decision confirmed; the 4 imported declarations confirmed dropped locally; risks
that bit; any statement change (there must be none); any promotion stopped on; `git status` showing
only the one new file.

## 8. Manager's half and results

Pre-wave, then worker, then manager review and wire.

**Pre-wave (manager).** `Definitions/Def_AutomorphicForm_ArchKFinite.lean` homed whole at
`AutomorphicForm/Adelic/ArchKFinite.lean` (9 declarations), tier-0 exit 0 / 0 warnings, tier-1
3.2 s; checker `9700 → 9709` (**+9**), 0 mismatched / 0 missing.

**Worker.** `Adelic/InducedSectionFlat.lean` — **528 lines, 33 public + 1 private**, tier-0 exit 0 /
0 warnings (5.76 s), tier-1 green (3,492 jobs, 4.0 s). Both headlines byte-equal to their
`Theorems/` wrappers (raw and normalized); all 33 declarations match their pin candidates. The 4
trusted substitutions are dropped and imported from tier 3 (`P6B.JE2aFlat.*`, `P6B.JE2aHMod.*`), and
`placeModulus` is kept as the pin's local explicit product — **not** replaced by `ideleNorm` (the
suspect row correctly not taken).

| check | result |
|---|---|
| checker | 9709 → **9742 identical — delta +33** (the 32 helpers plus the two headlines), 0 mismatched / 0 missing |
| `#print axioms` on both headlines | `[propext, Classical.choice, Quot.sound]` |
| register | current; totals unchanged (92 modules / 2,344 public / 2,056 with a pin original) |
| delimiters on this order | clean |

**Adaptations (proof-local; no statement changed, no promotion).**
`mul_lt_one_of_nonneg_of_lt_one_left` is deprecated in `v4.34.0` — its constituents
`(mul_le_of_le_one_right …).trans_lt hlt` are inlined in `norm_det_eq_one_of_integral`; node 2's
load-bearing `letI`/`haveI` carries one narrow `set_option linter.style.haveILetI false in`. The
file reproduces the pin's full `section`/`noncomputable section`/`end` ladder because Lean's
`end P6B.JE2aFlat` closes two scopes while the checker's parser counts one.

Wiring: both wrappers and their `S_` files appended last to `SOURCES`;
`FLTForHuman/AutomorphicForm/Adelic/InducedSectionFlat.lean` appended last to `PORT_FILES`.

**Step-6 re-read (successors).** Both nodes have left the ready shelf; it now reads 92 candidates.
The head is unchanged: `EisensteinGeneral.LocalRam.integral_twisted_smooth_eq` (864), then
`AutomorphicForm.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule` (823)
and `AlgebraicCurve.residue_norm_eq_norm_residue_of_retraction` (697).

Files changed: `FLTForHuman/AutomorphicForm/Adelic/ArchKFinite.lean` (new, pre-wave),
`FLTForHuman/AutomorphicForm/Adelic/InducedSectionFlat.lean` (new), `spec/old_check_stmts.py`,
`spec/UNWIRED-PUBLIC.md`.
